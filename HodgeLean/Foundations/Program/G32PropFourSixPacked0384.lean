import HodgeLean.Foundations.Program.G32PropFourSixPacked0382
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0383

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_029 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 29 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_029_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 0 15 15, g32p_row21_traceSegment_029_0000_0015, g32p_row21_traceSegment_029_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 30 15 15, g32p_row21_traceSegment_029_0030_0015, g32p_row21_traceSegment_029_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_029 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 0 30 30, g32p_row21_traceSegment_029_0000_0030, g32p_row21_traceSegment_029_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 60 15 15, g32p_row21_traceSegment_029_0060_0015, g32p_row21_traceSegment_029_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 90 15 16, g32p_row21_traceSegment_029_0090_0015, g32p_row21_traceSegment_029_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 60 30 31, g32p_row21_traceSegment_029_0060_0030, g32p_row21_traceSegment_029_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_029 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 0 60 61, g32p_row21_traceSegment_029_0000_0060, g32p_row21_traceSegment_029_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 121 15 15, g32p_row21_traceSegment_029_0121_0015, g32p_row21_traceSegment_029_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 151 15 16, g32p_row21_traceSegment_029_0151_0015, g32p_row21_traceSegment_029_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 121 30 31, g32p_row21_traceSegment_029_0121_0030, g32p_row21_traceSegment_029_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 182 15 15, g32p_row21_traceSegment_029_0182_0015, g32p_row21_traceSegment_029_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 212 15 16, g32p_row21_traceSegment_029_0212_0015, g32p_row21_traceSegment_029_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 182 30 31, g32p_row21_traceSegment_029_0182_0030, g32p_row21_traceSegment_029_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_029 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 121 61 61, g32p_row21_traceSegment_029_0121_0061, g32p_row21_traceSegment_029_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_029 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 0 121 122, g32p_row21_traceSegment_029_0000_0121, g32p_row21_traceSegment_029_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 243 15 15, g32p_row21_traceSegment_029_0243_0015, g32p_row21_traceSegment_029_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 273 15 15, g32p_row21_traceSegment_029_0273_0015, g32p_row21_traceSegment_029_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_029 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 243 30 30, g32p_row21_traceSegment_029_0243_0030, g32p_row21_traceSegment_029_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 303 15 15, g32p_row21_traceSegment_029_0303_0015, g32p_row21_traceSegment_029_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 333 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 348 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 333 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 333 15 16, g32p_row21_traceSegment_029_0333_0015, g32p_row21_traceSegment_029_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 303 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 303 30 31, g32p_row21_traceSegment_029_0303_0030, g32p_row21_traceSegment_029_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_029 243 121 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 243 60 61, g32p_row21_traceSegment_029_0243_0060, g32p_row21_traceSegment_029_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 364 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 364 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 364 15 15, g32p_row21_traceSegment_029_0364_0015, g32p_row21_traceSegment_029_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 394 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 394 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 394 15 16, g32p_row21_traceSegment_029_0394_0015, g32p_row21_traceSegment_029_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 364 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 364 30 31, g32p_row21_traceSegment_029_0364_0030, g32p_row21_traceSegment_029_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 425 15 15, g32p_row21_traceSegment_029_0425_0015, g32p_row21_traceSegment_029_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 455 15 16, g32p_row21_traceSegment_029_0455_0015, g32p_row21_traceSegment_029_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 425 30 31, g32p_row21_traceSegment_029_0425_0030, g32p_row21_traceSegment_029_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_029 364 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 364 61 61, g32p_row21_traceSegment_029_0364_0061, g32p_row21_traceSegment_029_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_029 243 243 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 243 121 122, g32p_row21_traceSegment_029_0243_0121, g32p_row21_traceSegment_029_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_029 0 486 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 0 243 243, g32p_row21_traceSegment_029_0000_0243, g32p_row21_traceSegment_029_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 486 15 15, g32p_row21_traceSegment_029_0486_0015, g32p_row21_traceSegment_029_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 516 15 15, g32p_row21_traceSegment_029_0516_0015, g32p_row21_traceSegment_029_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_029 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 486 30 30, g32p_row21_traceSegment_029_0486_0030, g32p_row21_traceSegment_029_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 546 15 15, g32p_row21_traceSegment_029_0546_0015, g32p_row21_traceSegment_029_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 576 15 16, g32p_row21_traceSegment_029_0576_0015, g32p_row21_traceSegment_029_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 546 30 31, g32p_row21_traceSegment_029_0546_0030, g32p_row21_traceSegment_029_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_029 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 486 60 61, g32p_row21_traceSegment_029_0486_0060, g32p_row21_traceSegment_029_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 607 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 622 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 607 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 607 15 15, g32p_row21_traceSegment_029_0607_0015, g32p_row21_traceSegment_029_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 637 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 637 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 637 15 16, g32p_row21_traceSegment_029_0637_0015, g32p_row21_traceSegment_029_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 607 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 607 30 31, g32p_row21_traceSegment_029_0607_0030, g32p_row21_traceSegment_029_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 668 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 683 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 668 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 668 15 15, g32p_row21_traceSegment_029_0668_0015, g32p_row21_traceSegment_029_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 698 15 16, g32p_row21_traceSegment_029_0698_0015, g32p_row21_traceSegment_029_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 668 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 668 30 31, g32p_row21_traceSegment_029_0668_0030, g32p_row21_traceSegment_029_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_029 607 122 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 607 61 61, g32p_row21_traceSegment_029_0607_0061, g32p_row21_traceSegment_029_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_029 486 243 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 486 121 122, g32p_row21_traceSegment_029_0486_0121, g32p_row21_traceSegment_029_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 729 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 729 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 729 15 15, g32p_row21_traceSegment_029_0729_0015, g32p_row21_traceSegment_029_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 759 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 759 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 759 15 15, g32p_row21_traceSegment_029_0759_0015, g32p_row21_traceSegment_029_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_029 729 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 729 30 30, g32p_row21_traceSegment_029_0729_0030, g32p_row21_traceSegment_029_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 804 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 789 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 789 15 15, g32p_row21_traceSegment_029_0789_0015, g32p_row21_traceSegment_029_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 819 15 16, g32p_row21_traceSegment_029_0819_0015, g32p_row21_traceSegment_029_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 789 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 789 30 31, g32p_row21_traceSegment_029_0789_0030, g32p_row21_traceSegment_029_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_029 729 121 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 729 60 61, g32p_row21_traceSegment_029_0729_0060, g32p_row21_traceSegment_029_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 850 15 15, g32p_row21_traceSegment_029_0850_0015, g32p_row21_traceSegment_029_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 895 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 880 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 880 15 16, g32p_row21_traceSegment_029_0880_0015, g32p_row21_traceSegment_029_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 850 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 850 30 31, g32p_row21_traceSegment_029_0850_0030, g32p_row21_traceSegment_029_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 911 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 926 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_029 911 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 911 15 15, g32p_row21_traceSegment_029_0911_0015, g32p_row21_traceSegment_029_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_029 941 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_029 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_029_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_029 941 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 941 15 16, g32p_row21_traceSegment_029_0941_0015, g32p_row21_traceSegment_029_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_029 911 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 911 30 31, g32p_row21_traceSegment_029_0911_0030, g32p_row21_traceSegment_029_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_029 850 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 850 61 61, g32p_row21_traceSegment_029_0850_0061, g32p_row21_traceSegment_029_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_029 729 243 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 729 121 122, g32p_row21_traceSegment_029_0729_0121, g32p_row21_traceSegment_029_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_029 486 486 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 486 243 243, g32p_row21_traceSegment_029_0486_0243, g32p_row21_traceSegment_029_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_029_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_029 0 972 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_029 0 486 486, g32p_row21_traceSegment_029_0000_0486, g32p_row21_traceSegment_029_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 29 = [0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_029_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_032 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 32 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_032_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 0 15 15, g32p_row21_traceSegment_032_0000_0015, g32p_row21_traceSegment_032_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 45 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 30 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 30 15 15, g32p_row21_traceSegment_032_0030_0015, g32p_row21_traceSegment_032_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_032 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 0 30 30, g32p_row21_traceSegment_032_0000_0030, g32p_row21_traceSegment_032_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 60 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 60 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 60 15 15, g32p_row21_traceSegment_032_0060_0015, g32p_row21_traceSegment_032_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 90 15 16, g32p_row21_traceSegment_032_0090_0015, g32p_row21_traceSegment_032_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 60 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 60 30 31, g32p_row21_traceSegment_032_0060_0030, g32p_row21_traceSegment_032_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_032 0 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 0 60 61, g32p_row21_traceSegment_032_0000_0060, g32p_row21_traceSegment_032_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 121 15 15, g32p_row21_traceSegment_032_0121_0015, g32p_row21_traceSegment_032_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 151 15 16, g32p_row21_traceSegment_032_0151_0015, g32p_row21_traceSegment_032_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 121 30 31, g32p_row21_traceSegment_032_0121_0030, g32p_row21_traceSegment_032_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 182 15 15, g32p_row21_traceSegment_032_0182_0015, g32p_row21_traceSegment_032_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 212 15 16, g32p_row21_traceSegment_032_0212_0015, g32p_row21_traceSegment_032_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 182 30 31, g32p_row21_traceSegment_032_0182_0030, g32p_row21_traceSegment_032_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_032 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 121 61 61, g32p_row21_traceSegment_032_0121_0061, g32p_row21_traceSegment_032_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_032 0 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 0 121 122, g32p_row21_traceSegment_032_0000_0121, g32p_row21_traceSegment_032_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 243 15 15, g32p_row21_traceSegment_032_0243_0015, g32p_row21_traceSegment_032_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 273 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 273 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 273 15 15, g32p_row21_traceSegment_032_0273_0015, g32p_row21_traceSegment_032_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_032 243 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 243 30 30, g32p_row21_traceSegment_032_0243_0030, g32p_row21_traceSegment_032_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 318 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 303 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 303 15 15, g32p_row21_traceSegment_032_0303_0015, g32p_row21_traceSegment_032_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 333 15 16, g32p_row21_traceSegment_032_0333_0015, g32p_row21_traceSegment_032_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 303 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 303 30 31, g32p_row21_traceSegment_032_0303_0030, g32p_row21_traceSegment_032_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_032 243 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 243 60 61, g32p_row21_traceSegment_032_0243_0060, g32p_row21_traceSegment_032_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 364 15 15, g32p_row21_traceSegment_032_0364_0015, g32p_row21_traceSegment_032_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 409 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 394 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 394 15 16, g32p_row21_traceSegment_032_0394_0015, g32p_row21_traceSegment_032_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 364 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 364 30 31, g32p_row21_traceSegment_032_0364_0030, g32p_row21_traceSegment_032_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 425 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 440 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 425 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 425 15 15, g32p_row21_traceSegment_032_0425_0015, g32p_row21_traceSegment_032_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 455 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 470 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 455 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 455 15 16, g32p_row21_traceSegment_032_0455_0015, g32p_row21_traceSegment_032_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 425 61 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 425 30 31, g32p_row21_traceSegment_032_0425_0030, g32p_row21_traceSegment_032_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_032 364 122 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 364 61 61, g32p_row21_traceSegment_032_0364_0061, g32p_row21_traceSegment_032_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_032 243 243 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 243 121 122, g32p_row21_traceSegment_032_0243_0121, g32p_row21_traceSegment_032_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_032 0 486 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 0 243 243, g32p_row21_traceSegment_032_0000_0243, g32p_row21_traceSegment_032_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 486 15 15, g32p_row21_traceSegment_032_0486_0015, g32p_row21_traceSegment_032_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 516 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 531 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 516 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 516 15 15, g32p_row21_traceSegment_032_0516_0015, g32p_row21_traceSegment_032_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_032 486 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 486 30 30, g32p_row21_traceSegment_032_0486_0030, g32p_row21_traceSegment_032_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 546 15 15, g32p_row21_traceSegment_032_0546_0015, g32p_row21_traceSegment_032_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 576 15 16, g32p_row21_traceSegment_032_0576_0015, g32p_row21_traceSegment_032_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 546 30 31, g32p_row21_traceSegment_032_0546_0030, g32p_row21_traceSegment_032_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_032 486 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 486 60 61, g32p_row21_traceSegment_032_0486_0060, g32p_row21_traceSegment_032_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 607 15 15, g32p_row21_traceSegment_032_0607_0015, g32p_row21_traceSegment_032_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 652 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 637 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 637 15 16, g32p_row21_traceSegment_032_0637_0015, g32p_row21_traceSegment_032_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 607 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 607 30 31, g32p_row21_traceSegment_032_0607_0030, g32p_row21_traceSegment_032_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 668 15 15, g32p_row21_traceSegment_032_0668_0015, g32p_row21_traceSegment_032_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 698 15 16, g32p_row21_traceSegment_032_0698_0015, g32p_row21_traceSegment_032_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 668 30 31, g32p_row21_traceSegment_032_0668_0030, g32p_row21_traceSegment_032_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_032 607 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 607 61 61, g32p_row21_traceSegment_032_0607_0061, g32p_row21_traceSegment_032_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_032 486 243 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 486 121 122, g32p_row21_traceSegment_032_0486_0121, g32p_row21_traceSegment_032_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 729 15 15, g32p_row21_traceSegment_032_0729_0015, g32p_row21_traceSegment_032_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 759 15 15, g32p_row21_traceSegment_032_0759_0015, g32p_row21_traceSegment_032_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_032 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 729 30 30, g32p_row21_traceSegment_032_0729_0030, g32p_row21_traceSegment_032_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 789 15 15, g32p_row21_traceSegment_032_0789_0015, g32p_row21_traceSegment_032_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 834 16 = [0, 1, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 819 31 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 819 15 16, g32p_row21_traceSegment_032_0819_0015, g32p_row21_traceSegment_032_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 789 61 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 789 30 31, g32p_row21_traceSegment_032_0789_0030, g32p_row21_traceSegment_032_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_032 729 121 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 729 60 61, g32p_row21_traceSegment_032_0729_0060, g32p_row21_traceSegment_032_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 850 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 865 15 = [0, 1, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 850 30 = [0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 850 15 15, g32p_row21_traceSegment_032_0850_0015, g32p_row21_traceSegment_032_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 880 15 = [1, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 895 16 = [1, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 880 31 = [2, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 880 15 16, g32p_row21_traceSegment_032_0880_0015, g32p_row21_traceSegment_032_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 850 61 = [2, 2, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 850 30 31, g32p_row21_traceSegment_032_0850_0030, g32p_row21_traceSegment_032_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 911 15 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 926 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_032 911 30 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 911 15 15, g32p_row21_traceSegment_032_0911_0015, g32p_row21_traceSegment_032_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_032 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_032 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_032_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_032 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 941 15 16, g32p_row21_traceSegment_032_0941_0015, g32p_row21_traceSegment_032_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_032 911 61 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 911 30 31, g32p_row21_traceSegment_032_0911_0030, g32p_row21_traceSegment_032_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_032 850 122 = [3, 2, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 850 61 61, g32p_row21_traceSegment_032_0850_0061, g32p_row21_traceSegment_032_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_032 729 243 = [3, 3, 10] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 729 121 122, g32p_row21_traceSegment_032_0729_0121, g32p_row21_traceSegment_032_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_032 486 486 = [3, 3, 13] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 486 243 243, g32p_row21_traceSegment_032_0486_0243, g32p_row21_traceSegment_032_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_032_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_032 0 972 = [3, 3, 24] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_032 0 486 486, g32p_row21_traceSegment_032_0000_0486, g32p_row21_traceSegment_032_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 32 = [3, 3, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_032_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_033 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 33 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_033_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 0 15 15, g32p_row21_traceSegment_033_0000_0015, g32p_row21_traceSegment_033_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 30 15 15, g32p_row21_traceSegment_033_0030_0015, g32p_row21_traceSegment_033_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_033 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 0 30 30, g32p_row21_traceSegment_033_0000_0030, g32p_row21_traceSegment_033_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 60 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 75 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 60 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 60 15 15, g32p_row21_traceSegment_033_0060_0015, g32p_row21_traceSegment_033_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 90 15 16, g32p_row21_traceSegment_033_0090_0015, g32p_row21_traceSegment_033_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 60 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 60 30 31, g32p_row21_traceSegment_033_0060_0030, g32p_row21_traceSegment_033_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_033 0 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 0 60 61, g32p_row21_traceSegment_033_0000_0060, g32p_row21_traceSegment_033_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 121 15 15, g32p_row21_traceSegment_033_0121_0015, g32p_row21_traceSegment_033_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 151 15 16, g32p_row21_traceSegment_033_0151_0015, g32p_row21_traceSegment_033_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 121 30 31, g32p_row21_traceSegment_033_0121_0030, g32p_row21_traceSegment_033_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 182 15 15, g32p_row21_traceSegment_033_0182_0015, g32p_row21_traceSegment_033_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 212 15 16, g32p_row21_traceSegment_033_0212_0015, g32p_row21_traceSegment_033_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 182 30 31, g32p_row21_traceSegment_033_0182_0030, g32p_row21_traceSegment_033_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_033 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 121 61 61, g32p_row21_traceSegment_033_0121_0061, g32p_row21_traceSegment_033_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_033 0 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 0 121 122, g32p_row21_traceSegment_033_0000_0121, g32p_row21_traceSegment_033_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 243 15 15, g32p_row21_traceSegment_033_0243_0015, g32p_row21_traceSegment_033_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 288 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 273 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 273 15 15, g32p_row21_traceSegment_033_0273_0015, g32p_row21_traceSegment_033_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_033 243 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 243 30 30, g32p_row21_traceSegment_033_0243_0030, g32p_row21_traceSegment_033_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 303 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 303 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 303 15 15, g32p_row21_traceSegment_033_0303_0015, g32p_row21_traceSegment_033_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 348 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 333 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 333 15 16, g32p_row21_traceSegment_033_0333_0015, g32p_row21_traceSegment_033_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 303 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 303 30 31, g32p_row21_traceSegment_033_0303_0030, g32p_row21_traceSegment_033_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_033 243 121 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 243 60 61, g32p_row21_traceSegment_033_0243_0060, g32p_row21_traceSegment_033_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 364 15 15, g32p_row21_traceSegment_033_0364_0015, g32p_row21_traceSegment_033_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 394 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 394 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 394 15 16, g32p_row21_traceSegment_033_0394_0015, g32p_row21_traceSegment_033_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 364 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 364 30 31, g32p_row21_traceSegment_033_0364_0030, g32p_row21_traceSegment_033_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 425 15 15, g32p_row21_traceSegment_033_0425_0015, g32p_row21_traceSegment_033_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 455 15 16, g32p_row21_traceSegment_033_0455_0015, g32p_row21_traceSegment_033_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 425 30 31, g32p_row21_traceSegment_033_0425_0030, g32p_row21_traceSegment_033_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_033 364 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 364 61 61, g32p_row21_traceSegment_033_0364_0061, g32p_row21_traceSegment_033_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_033 243 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 243 121 122, g32p_row21_traceSegment_033_0243_0121, g32p_row21_traceSegment_033_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_033 0 486 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 0 243 243, g32p_row21_traceSegment_033_0000_0243, g32p_row21_traceSegment_033_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 486 15 15, g32p_row21_traceSegment_033_0486_0015, g32p_row21_traceSegment_033_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 516 15 15, g32p_row21_traceSegment_033_0516_0015, g32p_row21_traceSegment_033_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_033 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 486 30 30, g32p_row21_traceSegment_033_0486_0030, g32p_row21_traceSegment_033_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 546 15 15, g32p_row21_traceSegment_033_0546_0015, g32p_row21_traceSegment_033_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 576 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 576 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 576 15 16, g32p_row21_traceSegment_033_0576_0015, g32p_row21_traceSegment_033_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 546 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 546 30 31, g32p_row21_traceSegment_033_0546_0030, g32p_row21_traceSegment_033_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_033 486 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 486 60 61, g32p_row21_traceSegment_033_0486_0060, g32p_row21_traceSegment_033_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 607 15 15, g32p_row21_traceSegment_033_0607_0015, g32p_row21_traceSegment_033_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 652 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 637 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 637 15 16, g32p_row21_traceSegment_033_0637_0015, g32p_row21_traceSegment_033_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 607 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 607 30 31, g32p_row21_traceSegment_033_0607_0030, g32p_row21_traceSegment_033_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 668 15 15, g32p_row21_traceSegment_033_0668_0015, g32p_row21_traceSegment_033_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 713 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 698 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 698 15 16, g32p_row21_traceSegment_033_0698_0015, g32p_row21_traceSegment_033_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 668 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 668 30 31, g32p_row21_traceSegment_033_0668_0030, g32p_row21_traceSegment_033_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_033 607 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 607 61 61, g32p_row21_traceSegment_033_0607_0061, g32p_row21_traceSegment_033_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_033 486 243 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 486 121 122, g32p_row21_traceSegment_033_0486_0121, g32p_row21_traceSegment_033_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 729 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 729 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 729 15 15, g32p_row21_traceSegment_033_0729_0015, g32p_row21_traceSegment_033_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 759 15 = [3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 759 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 759 15 15, g32p_row21_traceSegment_033_0759_0015, g32p_row21_traceSegment_033_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_033 729 60 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 729 30 30, g32p_row21_traceSegment_033_0729_0030, g32p_row21_traceSegment_033_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 804 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 789 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 789 15 15, g32p_row21_traceSegment_033_0789_0015, g32p_row21_traceSegment_033_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 819 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 819 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 819 15 16, g32p_row21_traceSegment_033_0819_0015, g32p_row21_traceSegment_033_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 789 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 789 30 31, g32p_row21_traceSegment_033_0789_0030, g32p_row21_traceSegment_033_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_033 729 121 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 729 60 61, g32p_row21_traceSegment_033_0729_0060, g32p_row21_traceSegment_033_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 850 15 15, g32p_row21_traceSegment_033_0850_0015, g32p_row21_traceSegment_033_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 880 15 16, g32p_row21_traceSegment_033_0880_0015, g32p_row21_traceSegment_033_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 850 30 31, g32p_row21_traceSegment_033_0850_0030, g32p_row21_traceSegment_033_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 926 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_033 911 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 911 15 15, g32p_row21_traceSegment_033_0911_0015, g32p_row21_traceSegment_033_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_033 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_033 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_033_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_033 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 941 15 16, g32p_row21_traceSegment_033_0941_0015, g32p_row21_traceSegment_033_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_033 911 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 911 30 31, g32p_row21_traceSegment_033_0911_0030, g32p_row21_traceSegment_033_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_033 850 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 850 61 61, g32p_row21_traceSegment_033_0850_0061, g32p_row21_traceSegment_033_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_033 729 243 = [8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 729 121 122, g32p_row21_traceSegment_033_0729_0121, g32p_row21_traceSegment_033_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_033 486 486 = [11] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 486 243 243, g32p_row21_traceSegment_033_0486_0243, g32p_row21_traceSegment_033_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_033_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_033 0 972 = [18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_033 0 486 486, g32p_row21_traceSegment_033_0000_0486, g32p_row21_traceSegment_033_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_033 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 33 = [18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_033_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_035 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 35 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_035_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 15 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 0 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 0 15 15, g32p_row21_traceSegment_035_0000_0015, g32p_row21_traceSegment_035_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 30 15 15, g32p_row21_traceSegment_035_0030_0015, g32p_row21_traceSegment_035_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_035 0 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 0 30 30, g32p_row21_traceSegment_035_0000_0030, g32p_row21_traceSegment_035_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 60 15 15, g32p_row21_traceSegment_035_0060_0015, g32p_row21_traceSegment_035_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 90 15 16, g32p_row21_traceSegment_035_0090_0015, g32p_row21_traceSegment_035_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 60 30 31, g32p_row21_traceSegment_035_0060_0030, g32p_row21_traceSegment_035_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_035 0 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 0 60 61, g32p_row21_traceSegment_035_0000_0060, g32p_row21_traceSegment_035_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 121 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 121 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 121 15 15, g32p_row21_traceSegment_035_0121_0015, g32p_row21_traceSegment_035_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 151 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 151 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 151 15 16, g32p_row21_traceSegment_035_0151_0015, g32p_row21_traceSegment_035_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 121 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 121 30 31, g32p_row21_traceSegment_035_0121_0030, g32p_row21_traceSegment_035_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 197 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 182 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 182 15 15, g32p_row21_traceSegment_035_0182_0015, g32p_row21_traceSegment_035_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 212 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 227 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 212 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 212 15 16, g32p_row21_traceSegment_035_0212_0015, g32p_row21_traceSegment_035_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 182 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 182 30 31, g32p_row21_traceSegment_035_0182_0030, g32p_row21_traceSegment_035_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_035 121 122 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 121 61 61, g32p_row21_traceSegment_035_0121_0061, g32p_row21_traceSegment_035_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_035 0 243 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 0 121 122, g32p_row21_traceSegment_035_0000_0121, g32p_row21_traceSegment_035_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 243 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 243 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 243 15 15, g32p_row21_traceSegment_035_0243_0015, g32p_row21_traceSegment_035_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 273 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 288 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 273 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 273 15 15, g32p_row21_traceSegment_035_0273_0015, g32p_row21_traceSegment_035_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_035 243 60 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 243 30 30, g32p_row21_traceSegment_035_0243_0030, g32p_row21_traceSegment_035_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 303 15 15, g32p_row21_traceSegment_035_0303_0015, g32p_row21_traceSegment_035_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 333 15 16, g32p_row21_traceSegment_035_0333_0015, g32p_row21_traceSegment_035_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 303 30 31, g32p_row21_traceSegment_035_0303_0030, g32p_row21_traceSegment_035_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_035 243 121 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 243 60 61, g32p_row21_traceSegment_035_0243_0060, g32p_row21_traceSegment_035_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 379 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 364 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 364 15 15, g32p_row21_traceSegment_035_0364_0015, g32p_row21_traceSegment_035_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 394 15 16, g32p_row21_traceSegment_035_0394_0015, g32p_row21_traceSegment_035_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 364 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 364 30 31, g32p_row21_traceSegment_035_0364_0030, g32p_row21_traceSegment_035_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 425 15 15, g32p_row21_traceSegment_035_0425_0015, g32p_row21_traceSegment_035_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 455 15 16, g32p_row21_traceSegment_035_0455_0015, g32p_row21_traceSegment_035_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 425 30 31, g32p_row21_traceSegment_035_0425_0030, g32p_row21_traceSegment_035_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_035 364 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 364 61 61, g32p_row21_traceSegment_035_0364_0061, g32p_row21_traceSegment_035_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_035 243 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 243 121 122, g32p_row21_traceSegment_035_0243_0121, g32p_row21_traceSegment_035_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_035 0 486 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 0 243 243, g32p_row21_traceSegment_035_0000_0243, g32p_row21_traceSegment_035_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 486 15 15, g32p_row21_traceSegment_035_0486_0015, g32p_row21_traceSegment_035_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 516 15 15, g32p_row21_traceSegment_035_0516_0015, g32p_row21_traceSegment_035_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_035 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 486 30 30, g32p_row21_traceSegment_035_0486_0030, g32p_row21_traceSegment_035_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 546 15 15, g32p_row21_traceSegment_035_0546_0015, g32p_row21_traceSegment_035_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 576 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 591 16 = [0, 1, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 576 31 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 576 15 16, g32p_row21_traceSegment_035_0576_0015, g32p_row21_traceSegment_035_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 546 61 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 546 30 31, g32p_row21_traceSegment_035_0546_0030, g32p_row21_traceSegment_035_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_035 486 121 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 486 60 61, g32p_row21_traceSegment_035_0486_0060, g32p_row21_traceSegment_035_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 607 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 622 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 607 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 607 15 15, g32p_row21_traceSegment_035_0607_0015, g32p_row21_traceSegment_035_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 637 15 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 652 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 637 31 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 637 15 16, g32p_row21_traceSegment_035_0637_0015, g32p_row21_traceSegment_035_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 607 61 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 607 30 31, g32p_row21_traceSegment_035_0607_0030, g32p_row21_traceSegment_035_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 668 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 668 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 668 15 15, g32p_row21_traceSegment_035_0668_0015, g32p_row21_traceSegment_035_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 698 15 = [1, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 713 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 698 31 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 698 15 16, g32p_row21_traceSegment_035_0698_0015, g32p_row21_traceSegment_035_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 668 61 = [3, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 668 30 31, g32p_row21_traceSegment_035_0668_0030, g32p_row21_traceSegment_035_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_035 607 122 = [3, 2, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 607 61 61, g32p_row21_traceSegment_035_0607_0061, g32p_row21_traceSegment_035_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_035 486 243 = [3, 3, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 486 121 122, g32p_row21_traceSegment_035_0486_0121, g32p_row21_traceSegment_035_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 729 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 729 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 729 15 15, g32p_row21_traceSegment_035_0729_0015, g32p_row21_traceSegment_035_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 774 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 759 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 759 15 15, g32p_row21_traceSegment_035_0759_0015, g32p_row21_traceSegment_035_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_035 729 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 729 30 30, g32p_row21_traceSegment_035_0729_0030, g32p_row21_traceSegment_035_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 789 15 15, g32p_row21_traceSegment_035_0789_0015, g32p_row21_traceSegment_035_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 819 15 16, g32p_row21_traceSegment_035_0819_0015, g32p_row21_traceSegment_035_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 789 30 31, g32p_row21_traceSegment_035_0789_0030, g32p_row21_traceSegment_035_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_035 729 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 729 60 61, g32p_row21_traceSegment_035_0729_0060, g32p_row21_traceSegment_035_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 850 15 15, g32p_row21_traceSegment_035_0850_0015, g32p_row21_traceSegment_035_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 880 15 16, g32p_row21_traceSegment_035_0880_0015, g32p_row21_traceSegment_035_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 850 30 31, g32p_row21_traceSegment_035_0850_0030, g32p_row21_traceSegment_035_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_035 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 911 15 15, g32p_row21_traceSegment_035_0911_0015, g32p_row21_traceSegment_035_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_035 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_035 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_035_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_035 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 941 15 16, g32p_row21_traceSegment_035_0941_0015, g32p_row21_traceSegment_035_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_035 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 911 30 31, g32p_row21_traceSegment_035_0911_0030, g32p_row21_traceSegment_035_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_035 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 850 61 61, g32p_row21_traceSegment_035_0850_0061, g32p_row21_traceSegment_035_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_035 729 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 729 121 122, g32p_row21_traceSegment_035_0729_0121, g32p_row21_traceSegment_035_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_035 486 486 = [3, 3, 10] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 486 243 243, g32p_row21_traceSegment_035_0486_0243, g32p_row21_traceSegment_035_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_035_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_035 0 972 = [3, 3, 24] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_035 0 486 486, g32p_row21_traceSegment_035_0000_0486, g32p_row21_traceSegment_035_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 35 = [3, 3, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_035_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_036 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 36 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_036_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 15 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 0 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 0 15 15, g32p_row21_traceSegment_036_0000_0015, g32p_row21_traceSegment_036_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 30 15 15, g32p_row21_traceSegment_036_0030_0015, g32p_row21_traceSegment_036_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_036 0 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 0 30 30, g32p_row21_traceSegment_036_0000_0030, g32p_row21_traceSegment_036_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 60 15 15, g32p_row21_traceSegment_036_0060_0015, g32p_row21_traceSegment_036_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 90 15 16, g32p_row21_traceSegment_036_0090_0015, g32p_row21_traceSegment_036_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 60 30 31, g32p_row21_traceSegment_036_0060_0030, g32p_row21_traceSegment_036_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_036 0 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 0 60 61, g32p_row21_traceSegment_036_0000_0060, g32p_row21_traceSegment_036_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 136 15 = [3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 121 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 121 15 15, g32p_row21_traceSegment_036_0121_0015, g32p_row21_traceSegment_036_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 166 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 151 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 151 15 16, g32p_row21_traceSegment_036_0151_0015, g32p_row21_traceSegment_036_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 121 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 121 30 31, g32p_row21_traceSegment_036_0121_0030, g32p_row21_traceSegment_036_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 182 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 182 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 182 15 15, g32p_row21_traceSegment_036_0182_0015, g32p_row21_traceSegment_036_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 212 15 16, g32p_row21_traceSegment_036_0212_0015, g32p_row21_traceSegment_036_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 182 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 182 30 31, g32p_row21_traceSegment_036_0182_0030, g32p_row21_traceSegment_036_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_036 121 122 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 121 61 61, g32p_row21_traceSegment_036_0121_0061, g32p_row21_traceSegment_036_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_036 0 243 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 0 121 122, g32p_row21_traceSegment_036_0000_0121, g32p_row21_traceSegment_036_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 243 15 15, g32p_row21_traceSegment_036_0243_0015, g32p_row21_traceSegment_036_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 273 15 15, g32p_row21_traceSegment_036_0273_0015, g32p_row21_traceSegment_036_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_036 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 243 30 30, g32p_row21_traceSegment_036_0243_0030, g32p_row21_traceSegment_036_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 318 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 303 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 303 15 15, g32p_row21_traceSegment_036_0303_0015, g32p_row21_traceSegment_036_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 333 15 16, g32p_row21_traceSegment_036_0333_0015, g32p_row21_traceSegment_036_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 303 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 303 30 31, g32p_row21_traceSegment_036_0303_0030, g32p_row21_traceSegment_036_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_036 243 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 243 60 61, g32p_row21_traceSegment_036_0243_0060, g32p_row21_traceSegment_036_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 379 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 364 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 364 15 15, g32p_row21_traceSegment_036_0364_0015, g32p_row21_traceSegment_036_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 394 15 16, g32p_row21_traceSegment_036_0394_0015, g32p_row21_traceSegment_036_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 364 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 364 30 31, g32p_row21_traceSegment_036_0364_0030, g32p_row21_traceSegment_036_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 440 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 425 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 425 15 15, g32p_row21_traceSegment_036_0425_0015, g32p_row21_traceSegment_036_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 470 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 455 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 455 15 16, g32p_row21_traceSegment_036_0455_0015, g32p_row21_traceSegment_036_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 425 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 425 30 31, g32p_row21_traceSegment_036_0425_0030, g32p_row21_traceSegment_036_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_036 364 122 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 364 61 61, g32p_row21_traceSegment_036_0364_0061, g32p_row21_traceSegment_036_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_036 243 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 243 121 122, g32p_row21_traceSegment_036_0243_0121, g32p_row21_traceSegment_036_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_036 0 486 = [12] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 0 243 243, g32p_row21_traceSegment_036_0000_0243, g32p_row21_traceSegment_036_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 486 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 501 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 486 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 486 15 15, g32p_row21_traceSegment_036_0486_0015, g32p_row21_traceSegment_036_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 531 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 516 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 516 15 15, g32p_row21_traceSegment_036_0516_0015, g32p_row21_traceSegment_036_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_036 486 60 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 486 30 30, g32p_row21_traceSegment_036_0486_0030, g32p_row21_traceSegment_036_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 561 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 546 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 546 15 15, g32p_row21_traceSegment_036_0546_0015, g32p_row21_traceSegment_036_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 576 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 576 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 576 15 16, g32p_row21_traceSegment_036_0576_0015, g32p_row21_traceSegment_036_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 546 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 546 30 31, g32p_row21_traceSegment_036_0546_0030, g32p_row21_traceSegment_036_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_036 486 121 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 486 60 61, g32p_row21_traceSegment_036_0486_0060, g32p_row21_traceSegment_036_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 607 15 15, g32p_row21_traceSegment_036_0607_0015, g32p_row21_traceSegment_036_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 637 15 16, g32p_row21_traceSegment_036_0637_0015, g32p_row21_traceSegment_036_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 607 30 31, g32p_row21_traceSegment_036_0607_0030, g32p_row21_traceSegment_036_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 668 15 15, g32p_row21_traceSegment_036_0668_0015, g32p_row21_traceSegment_036_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 698 15 16, g32p_row21_traceSegment_036_0698_0015, g32p_row21_traceSegment_036_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 668 30 31, g32p_row21_traceSegment_036_0668_0030, g32p_row21_traceSegment_036_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_036 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 607 61 61, g32p_row21_traceSegment_036_0607_0061, g32p_row21_traceSegment_036_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_036 486 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 486 121 122, g32p_row21_traceSegment_036_0486_0121, g32p_row21_traceSegment_036_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 729 15 15, g32p_row21_traceSegment_036_0729_0015, g32p_row21_traceSegment_036_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 774 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 759 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 759 15 15, g32p_row21_traceSegment_036_0759_0015, g32p_row21_traceSegment_036_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_036 729 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 729 30 30, g32p_row21_traceSegment_036_0729_0030, g32p_row21_traceSegment_036_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 789 15 15, g32p_row21_traceSegment_036_0789_0015, g32p_row21_traceSegment_036_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 819 15 16, g32p_row21_traceSegment_036_0819_0015, g32p_row21_traceSegment_036_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 789 30 31, g32p_row21_traceSegment_036_0789_0030, g32p_row21_traceSegment_036_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_036 729 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 729 60 61, g32p_row21_traceSegment_036_0729_0060, g32p_row21_traceSegment_036_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 850 15 15, g32p_row21_traceSegment_036_0850_0015, g32p_row21_traceSegment_036_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 880 15 16, g32p_row21_traceSegment_036_0880_0015, g32p_row21_traceSegment_036_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 850 30 31, g32p_row21_traceSegment_036_0850_0030, g32p_row21_traceSegment_036_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_036 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 911 15 15, g32p_row21_traceSegment_036_0911_0015, g32p_row21_traceSegment_036_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_036 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_036 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_036_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_036 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 941 15 16, g32p_row21_traceSegment_036_0941_0015, g32p_row21_traceSegment_036_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_036 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 911 30 31, g32p_row21_traceSegment_036_0911_0030, g32p_row21_traceSegment_036_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_036 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 850 61 61, g32p_row21_traceSegment_036_0850_0061, g32p_row21_traceSegment_036_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_036 729 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 729 121 122, g32p_row21_traceSegment_036_0729_0121, g32p_row21_traceSegment_036_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_036 486 486 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 486 243 243, g32p_row21_traceSegment_036_0486_0243, g32p_row21_traceSegment_036_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_036_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_036 0 972 = [18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_036 0 486 486, g32p_row21_traceSegment_036_0000_0486, g32p_row21_traceSegment_036_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_036 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 36 = [18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_036_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row21_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 24) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 24) (g32p_literalTraceValue 20 24)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row21_traceCoefficients_024]
  decide +kernel

theorem g32p_row21_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 25) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 25) (g32p_literalTraceValue 20 25)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row21_traceCoefficients_025]
  decide +kernel

theorem g32p_row21_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 28) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 28) (g32p_literalTraceValue 20 28)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_028]
  decide +kernel

theorem g32p_row21_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 29) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 29) (g32p_literalTraceValue 20 29)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_029]
  decide +kernel

theorem g32p_row21_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 32) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 32) (g32p_literalTraceValue 20 32)
      [1, 1, 1] [7776] = true := by
  rw [g32p_row21_traceCoefficients_032]
  decide +kernel

theorem g32p_row21_tracePolynomial_033 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 33) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 33) (g32p_literalTraceValue 20 33)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_033]
  decide +kernel

theorem g32p_row21_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 35) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 35) (g32p_literalTraceValue 20 35)
      [1, 1, 1] [7776] = true := by
  rw [g32p_row21_traceCoefficients_035]
  decide +kernel

theorem g32p_row21_tracePolynomial_036 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 36) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 36) (g32p_literalTraceValue 20 36)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_036]
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

private def g32p_row21_traceSegment_037 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 37 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_037_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 0 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 0 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 0 15 15, g32p_row21_traceSegment_037_0000_0015, g32p_row21_traceSegment_037_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 30 15 15, g32p_row21_traceSegment_037_0030_0015, g32p_row21_traceSegment_037_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_037 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 0 30 30, g32p_row21_traceSegment_037_0000_0030, g32p_row21_traceSegment_037_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 60 15 15, g32p_row21_traceSegment_037_0060_0015, g32p_row21_traceSegment_037_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 90 15 16, g32p_row21_traceSegment_037_0090_0015, g32p_row21_traceSegment_037_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 60 30 31, g32p_row21_traceSegment_037_0060_0030, g32p_row21_traceSegment_037_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_037 0 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 0 60 61, g32p_row21_traceSegment_037_0000_0060, g32p_row21_traceSegment_037_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 121 15 15, g32p_row21_traceSegment_037_0121_0015, g32p_row21_traceSegment_037_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 151 15 16, g32p_row21_traceSegment_037_0151_0015, g32p_row21_traceSegment_037_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 121 30 31, g32p_row21_traceSegment_037_0121_0030, g32p_row21_traceSegment_037_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 182 15 15, g32p_row21_traceSegment_037_0182_0015, g32p_row21_traceSegment_037_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 212 15 16, g32p_row21_traceSegment_037_0212_0015, g32p_row21_traceSegment_037_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 182 30 31, g32p_row21_traceSegment_037_0182_0030, g32p_row21_traceSegment_037_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_037 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 121 61 61, g32p_row21_traceSegment_037_0121_0061, g32p_row21_traceSegment_037_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_037 0 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 0 121 122, g32p_row21_traceSegment_037_0000_0121, g32p_row21_traceSegment_037_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 243 15 15, g32p_row21_traceSegment_037_0243_0015, g32p_row21_traceSegment_037_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 273 15 15, g32p_row21_traceSegment_037_0273_0015, g32p_row21_traceSegment_037_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_037 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 243 30 30, g32p_row21_traceSegment_037_0243_0030, g32p_row21_traceSegment_037_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 303 15 15, g32p_row21_traceSegment_037_0303_0015, g32p_row21_traceSegment_037_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 333 15 16, g32p_row21_traceSegment_037_0333_0015, g32p_row21_traceSegment_037_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 303 30 31, g32p_row21_traceSegment_037_0303_0030, g32p_row21_traceSegment_037_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_037 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 243 60 61, g32p_row21_traceSegment_037_0243_0060, g32p_row21_traceSegment_037_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 364 15 15, g32p_row21_traceSegment_037_0364_0015, g32p_row21_traceSegment_037_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 394 15 16, g32p_row21_traceSegment_037_0394_0015, g32p_row21_traceSegment_037_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 364 30 31, g32p_row21_traceSegment_037_0364_0030, g32p_row21_traceSegment_037_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 425 15 15, g32p_row21_traceSegment_037_0425_0015, g32p_row21_traceSegment_037_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 455 15 16, g32p_row21_traceSegment_037_0455_0015, g32p_row21_traceSegment_037_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 425 30 31, g32p_row21_traceSegment_037_0425_0030, g32p_row21_traceSegment_037_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_037 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 364 61 61, g32p_row21_traceSegment_037_0364_0061, g32p_row21_traceSegment_037_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_037 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 243 121 122, g32p_row21_traceSegment_037_0243_0121, g32p_row21_traceSegment_037_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_037 0 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 0 243 243, g32p_row21_traceSegment_037_0000_0243, g32p_row21_traceSegment_037_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 486 15 15, g32p_row21_traceSegment_037_0486_0015, g32p_row21_traceSegment_037_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 516 15 15, g32p_row21_traceSegment_037_0516_0015, g32p_row21_traceSegment_037_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_037 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 486 30 30, g32p_row21_traceSegment_037_0486_0030, g32p_row21_traceSegment_037_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 546 15 15, g32p_row21_traceSegment_037_0546_0015, g32p_row21_traceSegment_037_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 576 15 16, g32p_row21_traceSegment_037_0576_0015, g32p_row21_traceSegment_037_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 546 30 31, g32p_row21_traceSegment_037_0546_0030, g32p_row21_traceSegment_037_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_037 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 486 60 61, g32p_row21_traceSegment_037_0486_0060, g32p_row21_traceSegment_037_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 607 15 15, g32p_row21_traceSegment_037_0607_0015, g32p_row21_traceSegment_037_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 637 15 16, g32p_row21_traceSegment_037_0637_0015, g32p_row21_traceSegment_037_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 607 30 31, g32p_row21_traceSegment_037_0607_0030, g32p_row21_traceSegment_037_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 668 15 15, g32p_row21_traceSegment_037_0668_0015, g32p_row21_traceSegment_037_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 698 15 16, g32p_row21_traceSegment_037_0698_0015, g32p_row21_traceSegment_037_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 668 30 31, g32p_row21_traceSegment_037_0668_0030, g32p_row21_traceSegment_037_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_037 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 607 61 61, g32p_row21_traceSegment_037_0607_0061, g32p_row21_traceSegment_037_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_037 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 486 121 122, g32p_row21_traceSegment_037_0486_0121, g32p_row21_traceSegment_037_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 729 15 15, g32p_row21_traceSegment_037_0729_0015, g32p_row21_traceSegment_037_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 759 15 15, g32p_row21_traceSegment_037_0759_0015, g32p_row21_traceSegment_037_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_037 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 729 30 30, g32p_row21_traceSegment_037_0729_0030, g32p_row21_traceSegment_037_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 789 15 15, g32p_row21_traceSegment_037_0789_0015, g32p_row21_traceSegment_037_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 819 15 16, g32p_row21_traceSegment_037_0819_0015, g32p_row21_traceSegment_037_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 789 30 31, g32p_row21_traceSegment_037_0789_0030, g32p_row21_traceSegment_037_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_037 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 729 60 61, g32p_row21_traceSegment_037_0729_0060, g32p_row21_traceSegment_037_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 850 15 15, g32p_row21_traceSegment_037_0850_0015, g32p_row21_traceSegment_037_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 880 15 16, g32p_row21_traceSegment_037_0880_0015, g32p_row21_traceSegment_037_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 850 30 31, g32p_row21_traceSegment_037_0850_0030, g32p_row21_traceSegment_037_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_037 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 911 15 15, g32p_row21_traceSegment_037_0911_0015, g32p_row21_traceSegment_037_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_037 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_037 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_037_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_037 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 941 15 16, g32p_row21_traceSegment_037_0941_0015, g32p_row21_traceSegment_037_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_037 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 911 30 31, g32p_row21_traceSegment_037_0911_0030, g32p_row21_traceSegment_037_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_037 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 850 61 61, g32p_row21_traceSegment_037_0850_0061, g32p_row21_traceSegment_037_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_037 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 729 121 122, g32p_row21_traceSegment_037_0729_0121, g32p_row21_traceSegment_037_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_037 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 486 243 243, g32p_row21_traceSegment_037_0486_0243, g32p_row21_traceSegment_037_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_037_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_037 0 972 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_037 0 486 486, g32p_row21_traceSegment_037_0000_0486, g32p_row21_traceSegment_037_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 37 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_037_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_039 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 39 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_039_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 0 15 15, g32p_row21_traceSegment_039_0000_0015, g32p_row21_traceSegment_039_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 30 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 45 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 30 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 30 15 15, g32p_row21_traceSegment_039_0030_0015, g32p_row21_traceSegment_039_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_039 0 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 0 30 30, g32p_row21_traceSegment_039_0000_0030, g32p_row21_traceSegment_039_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 60 15 15, g32p_row21_traceSegment_039_0060_0015, g32p_row21_traceSegment_039_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 90 15 16, g32p_row21_traceSegment_039_0090_0015, g32p_row21_traceSegment_039_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 60 30 31, g32p_row21_traceSegment_039_0060_0030, g32p_row21_traceSegment_039_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_039 0 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 0 60 61, g32p_row21_traceSegment_039_0000_0060, g32p_row21_traceSegment_039_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 121 15 15, g32p_row21_traceSegment_039_0121_0015, g32p_row21_traceSegment_039_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 166 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 151 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 151 15 16, g32p_row21_traceSegment_039_0151_0015, g32p_row21_traceSegment_039_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 121 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 121 30 31, g32p_row21_traceSegment_039_0121_0030, g32p_row21_traceSegment_039_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 182 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 182 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 182 15 15, g32p_row21_traceSegment_039_0182_0015, g32p_row21_traceSegment_039_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 227 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 212 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 212 15 16, g32p_row21_traceSegment_039_0212_0015, g32p_row21_traceSegment_039_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 182 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 182 30 31, g32p_row21_traceSegment_039_0182_0030, g32p_row21_traceSegment_039_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_039 121 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 121 61 61, g32p_row21_traceSegment_039_0121_0061, g32p_row21_traceSegment_039_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_039 0 243 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 0 121 122, g32p_row21_traceSegment_039_0000_0121, g32p_row21_traceSegment_039_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 243 15 15, g32p_row21_traceSegment_039_0243_0015, g32p_row21_traceSegment_039_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 273 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 273 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 273 15 15, g32p_row21_traceSegment_039_0273_0015, g32p_row21_traceSegment_039_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_039 243 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 243 30 30, g32p_row21_traceSegment_039_0243_0030, g32p_row21_traceSegment_039_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 303 15 15, g32p_row21_traceSegment_039_0303_0015, g32p_row21_traceSegment_039_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 333 15 16, g32p_row21_traceSegment_039_0333_0015, g32p_row21_traceSegment_039_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 303 30 31, g32p_row21_traceSegment_039_0303_0030, g32p_row21_traceSegment_039_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_039 243 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 243 60 61, g32p_row21_traceSegment_039_0243_0060, g32p_row21_traceSegment_039_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 364 15 15, g32p_row21_traceSegment_039_0364_0015, g32p_row21_traceSegment_039_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 394 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 394 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 394 15 16, g32p_row21_traceSegment_039_0394_0015, g32p_row21_traceSegment_039_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 364 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 364 30 31, g32p_row21_traceSegment_039_0364_0030, g32p_row21_traceSegment_039_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 425 15 15, g32p_row21_traceSegment_039_0425_0015, g32p_row21_traceSegment_039_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 455 15 16, g32p_row21_traceSegment_039_0455_0015, g32p_row21_traceSegment_039_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 425 30 31, g32p_row21_traceSegment_039_0425_0030, g32p_row21_traceSegment_039_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_039 364 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 364 61 61, g32p_row21_traceSegment_039_0364_0061, g32p_row21_traceSegment_039_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_039 243 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 243 121 122, g32p_row21_traceSegment_039_0243_0121, g32p_row21_traceSegment_039_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_039 0 486 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 0 243 243, g32p_row21_traceSegment_039_0000_0243, g32p_row21_traceSegment_039_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 486 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 486 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 486 15 15, g32p_row21_traceSegment_039_0486_0015, g32p_row21_traceSegment_039_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 516 15 15, g32p_row21_traceSegment_039_0516_0015, g32p_row21_traceSegment_039_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_039 486 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 486 30 30, g32p_row21_traceSegment_039_0486_0030, g32p_row21_traceSegment_039_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 546 15 15, g32p_row21_traceSegment_039_0546_0015, g32p_row21_traceSegment_039_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 576 15 16, g32p_row21_traceSegment_039_0576_0015, g32p_row21_traceSegment_039_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 546 30 31, g32p_row21_traceSegment_039_0546_0030, g32p_row21_traceSegment_039_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_039 486 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 486 60 61, g32p_row21_traceSegment_039_0486_0060, g32p_row21_traceSegment_039_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 622 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 607 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 607 15 15, g32p_row21_traceSegment_039_0607_0015, g32p_row21_traceSegment_039_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 637 15 16, g32p_row21_traceSegment_039_0637_0015, g32p_row21_traceSegment_039_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 607 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 607 30 31, g32p_row21_traceSegment_039_0607_0030, g32p_row21_traceSegment_039_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 668 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 668 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 668 15 15, g32p_row21_traceSegment_039_0668_0015, g32p_row21_traceSegment_039_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 698 15 16, g32p_row21_traceSegment_039_0698_0015, g32p_row21_traceSegment_039_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 668 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 668 30 31, g32p_row21_traceSegment_039_0668_0030, g32p_row21_traceSegment_039_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_039 607 122 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 607 61 61, g32p_row21_traceSegment_039_0607_0061, g32p_row21_traceSegment_039_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_039 486 243 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 486 121 122, g32p_row21_traceSegment_039_0486_0121, g32p_row21_traceSegment_039_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 729 15 15, g32p_row21_traceSegment_039_0729_0015, g32p_row21_traceSegment_039_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 759 15 15, g32p_row21_traceSegment_039_0759_0015, g32p_row21_traceSegment_039_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_039 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 729 30 30, g32p_row21_traceSegment_039_0729_0030, g32p_row21_traceSegment_039_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 789 15 15, g32p_row21_traceSegment_039_0789_0015, g32p_row21_traceSegment_039_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 834 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 819 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 819 15 16, g32p_row21_traceSegment_039_0819_0015, g32p_row21_traceSegment_039_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 789 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 789 30 31, g32p_row21_traceSegment_039_0789_0030, g32p_row21_traceSegment_039_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_039 729 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 729 60 61, g32p_row21_traceSegment_039_0729_0060, g32p_row21_traceSegment_039_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 850 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 850 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 850 15 15, g32p_row21_traceSegment_039_0850_0015, g32p_row21_traceSegment_039_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 880 15 16, g32p_row21_traceSegment_039_0880_0015, g32p_row21_traceSegment_039_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 850 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 850 30 31, g32p_row21_traceSegment_039_0850_0030, g32p_row21_traceSegment_039_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_039 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 911 15 15, g32p_row21_traceSegment_039_0911_0015, g32p_row21_traceSegment_039_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_039 941 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_039 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_039_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_039 941 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 941 15 16, g32p_row21_traceSegment_039_0941_0015, g32p_row21_traceSegment_039_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_039 911 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 911 30 31, g32p_row21_traceSegment_039_0911_0030, g32p_row21_traceSegment_039_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_039 850 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 850 61 61, g32p_row21_traceSegment_039_0850_0061, g32p_row21_traceSegment_039_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_039 729 243 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 729 121 122, g32p_row21_traceSegment_039_0729_0121, g32p_row21_traceSegment_039_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_039 486 486 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 486 243 243, g32p_row21_traceSegment_039_0486_0243, g32p_row21_traceSegment_039_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_039_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_039 0 972 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_039 0 486 486, g32p_row21_traceSegment_039_0000_0486, g32p_row21_traceSegment_039_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_039 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 39 = [0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_039_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_040 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 40 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_040_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 0 15 15, g32p_row21_traceSegment_040_0000_0015, g32p_row21_traceSegment_040_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 30 15 15, g32p_row21_traceSegment_040_0030_0015, g32p_row21_traceSegment_040_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_040 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 0 30 30, g32p_row21_traceSegment_040_0000_0030, g32p_row21_traceSegment_040_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 60 15 15, g32p_row21_traceSegment_040_0060_0015, g32p_row21_traceSegment_040_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 90 15 16, g32p_row21_traceSegment_040_0090_0015, g32p_row21_traceSegment_040_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 60 30 31, g32p_row21_traceSegment_040_0060_0030, g32p_row21_traceSegment_040_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_040 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 0 60 61, g32p_row21_traceSegment_040_0000_0060, g32p_row21_traceSegment_040_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 121 15 15, g32p_row21_traceSegment_040_0121_0015, g32p_row21_traceSegment_040_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 151 15 16, g32p_row21_traceSegment_040_0151_0015, g32p_row21_traceSegment_040_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 121 30 31, g32p_row21_traceSegment_040_0121_0030, g32p_row21_traceSegment_040_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 197 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 182 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 182 15 15, g32p_row21_traceSegment_040_0182_0015, g32p_row21_traceSegment_040_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 227 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 212 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 212 15 16, g32p_row21_traceSegment_040_0212_0015, g32p_row21_traceSegment_040_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 182 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 182 30 31, g32p_row21_traceSegment_040_0182_0030, g32p_row21_traceSegment_040_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_040 121 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 121 61 61, g32p_row21_traceSegment_040_0121_0061, g32p_row21_traceSegment_040_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_040 0 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 0 121 122, g32p_row21_traceSegment_040_0000_0121, g32p_row21_traceSegment_040_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 258 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 243 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 243 15 15, g32p_row21_traceSegment_040_0243_0015, g32p_row21_traceSegment_040_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 273 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 288 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 273 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 273 15 15, g32p_row21_traceSegment_040_0273_0015, g32p_row21_traceSegment_040_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_040 243 60 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 243 30 30, g32p_row21_traceSegment_040_0243_0030, g32p_row21_traceSegment_040_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 318 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 303 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 303 15 15, g32p_row21_traceSegment_040_0303_0015, g32p_row21_traceSegment_040_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 348 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 333 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 333 15 16, g32p_row21_traceSegment_040_0333_0015, g32p_row21_traceSegment_040_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 303 61 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 303 30 31, g32p_row21_traceSegment_040_0303_0030, g32p_row21_traceSegment_040_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_040 243 121 = [0, 2, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 243 60 61, g32p_row21_traceSegment_040_0243_0060, g32p_row21_traceSegment_040_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 379 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 364 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 364 15 15, g32p_row21_traceSegment_040_0364_0015, g32p_row21_traceSegment_040_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 394 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 394 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 394 15 16, g32p_row21_traceSegment_040_0394_0015, g32p_row21_traceSegment_040_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 364 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 364 30 31, g32p_row21_traceSegment_040_0364_0030, g32p_row21_traceSegment_040_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 425 15 15, g32p_row21_traceSegment_040_0425_0015, g32p_row21_traceSegment_040_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 455 15 16, g32p_row21_traceSegment_040_0455_0015, g32p_row21_traceSegment_040_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 425 30 31, g32p_row21_traceSegment_040_0425_0030, g32p_row21_traceSegment_040_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_040 364 122 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 364 61 61, g32p_row21_traceSegment_040_0364_0061, g32p_row21_traceSegment_040_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_040 243 243 = [0, 5, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 243 121 122, g32p_row21_traceSegment_040_0243_0121, g32p_row21_traceSegment_040_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_040 0 486 = [0, 5, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 0 243 243, g32p_row21_traceSegment_040_0000_0243, g32p_row21_traceSegment_040_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 486 15 15, g32p_row21_traceSegment_040_0486_0015, g32p_row21_traceSegment_040_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 516 15 15, g32p_row21_traceSegment_040_0516_0015, g32p_row21_traceSegment_040_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_040 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 486 30 30, g32p_row21_traceSegment_040_0486_0030, g32p_row21_traceSegment_040_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 546 15 15, g32p_row21_traceSegment_040_0546_0015, g32p_row21_traceSegment_040_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 576 15 16, g32p_row21_traceSegment_040_0576_0015, g32p_row21_traceSegment_040_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 546 30 31, g32p_row21_traceSegment_040_0546_0030, g32p_row21_traceSegment_040_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_040 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 486 60 61, g32p_row21_traceSegment_040_0486_0060, g32p_row21_traceSegment_040_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 607 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 607 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 607 15 15, g32p_row21_traceSegment_040_0607_0015, g32p_row21_traceSegment_040_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 637 15 16, g32p_row21_traceSegment_040_0637_0015, g32p_row21_traceSegment_040_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 607 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 607 30 31, g32p_row21_traceSegment_040_0607_0030, g32p_row21_traceSegment_040_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 668 15 15, g32p_row21_traceSegment_040_0668_0015, g32p_row21_traceSegment_040_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 713 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 698 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 698 15 16, g32p_row21_traceSegment_040_0698_0015, g32p_row21_traceSegment_040_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 668 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 668 30 31, g32p_row21_traceSegment_040_0668_0030, g32p_row21_traceSegment_040_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_040 607 122 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 607 61 61, g32p_row21_traceSegment_040_0607_0061, g32p_row21_traceSegment_040_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_040 486 243 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 486 121 122, g32p_row21_traceSegment_040_0486_0121, g32p_row21_traceSegment_040_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 744 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 729 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 729 15 15, g32p_row21_traceSegment_040_0729_0015, g32p_row21_traceSegment_040_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 759 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 759 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 759 15 15, g32p_row21_traceSegment_040_0759_0015, g32p_row21_traceSegment_040_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_040 729 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 729 30 30, g32p_row21_traceSegment_040_0729_0030, g32p_row21_traceSegment_040_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 789 15 15, g32p_row21_traceSegment_040_0789_0015, g32p_row21_traceSegment_040_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 819 15 16, g32p_row21_traceSegment_040_0819_0015, g32p_row21_traceSegment_040_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 789 30 31, g32p_row21_traceSegment_040_0789_0030, g32p_row21_traceSegment_040_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_040 729 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 729 60 61, g32p_row21_traceSegment_040_0729_0060, g32p_row21_traceSegment_040_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 850 15 15, g32p_row21_traceSegment_040_0850_0015, g32p_row21_traceSegment_040_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 880 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 880 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 880 15 16, g32p_row21_traceSegment_040_0880_0015, g32p_row21_traceSegment_040_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 850 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 850 30 31, g32p_row21_traceSegment_040_0850_0030, g32p_row21_traceSegment_040_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_040 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 911 15 15, g32p_row21_traceSegment_040_0911_0015, g32p_row21_traceSegment_040_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_040 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_040 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_040_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_040 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 941 15 16, g32p_row21_traceSegment_040_0941_0015, g32p_row21_traceSegment_040_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_040 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 911 30 31, g32p_row21_traceSegment_040_0911_0030, g32p_row21_traceSegment_040_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_040 850 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 850 61 61, g32p_row21_traceSegment_040_0850_0061, g32p_row21_traceSegment_040_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_040 729 243 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 729 121 122, g32p_row21_traceSegment_040_0729_0121, g32p_row21_traceSegment_040_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_040 486 486 = [0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 486 243 243, g32p_row21_traceSegment_040_0486_0243, g32p_row21_traceSegment_040_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_040_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_040 0 972 = [0, 9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_040 0 486 486, g32p_row21_traceSegment_040_0000_0486, g32p_row21_traceSegment_040_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 40 = [0, 9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_040_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_042 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 42 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_042_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 0 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 15 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 0 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 0 15 15, g32p_row21_traceSegment_042_0000_0015, g32p_row21_traceSegment_042_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 30 15 15, g32p_row21_traceSegment_042_0030_0015, g32p_row21_traceSegment_042_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_042 0 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 0 30 30, g32p_row21_traceSegment_042_0000_0030, g32p_row21_traceSegment_042_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 60 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 75 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 60 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 60 15 15, g32p_row21_traceSegment_042_0060_0015, g32p_row21_traceSegment_042_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 105 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 90 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 90 15 16, g32p_row21_traceSegment_042_0090_0015, g32p_row21_traceSegment_042_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 60 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 60 30 31, g32p_row21_traceSegment_042_0060_0030, g32p_row21_traceSegment_042_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_042 0 121 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 0 60 61, g32p_row21_traceSegment_042_0000_0060, g32p_row21_traceSegment_042_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 121 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 121 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 121 15 15, g32p_row21_traceSegment_042_0121_0015, g32p_row21_traceSegment_042_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 151 15 16, g32p_row21_traceSegment_042_0151_0015, g32p_row21_traceSegment_042_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 121 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 121 30 31, g32p_row21_traceSegment_042_0121_0030, g32p_row21_traceSegment_042_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 197 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 182 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 182 15 15, g32p_row21_traceSegment_042_0182_0015, g32p_row21_traceSegment_042_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 212 15 16, g32p_row21_traceSegment_042_0212_0015, g32p_row21_traceSegment_042_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 182 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 182 30 31, g32p_row21_traceSegment_042_0182_0030, g32p_row21_traceSegment_042_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_042 121 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 121 61 61, g32p_row21_traceSegment_042_0121_0061, g32p_row21_traceSegment_042_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_042 0 243 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 0 121 122, g32p_row21_traceSegment_042_0000_0121, g32p_row21_traceSegment_042_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 258 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 243 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 243 15 15, g32p_row21_traceSegment_042_0243_0015, g32p_row21_traceSegment_042_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 273 15 15, g32p_row21_traceSegment_042_0273_0015, g32p_row21_traceSegment_042_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_042 243 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 243 30 30, g32p_row21_traceSegment_042_0243_0030, g32p_row21_traceSegment_042_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 303 15 15, g32p_row21_traceSegment_042_0303_0015, g32p_row21_traceSegment_042_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 348 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 333 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 333 15 16, g32p_row21_traceSegment_042_0333_0015, g32p_row21_traceSegment_042_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 303 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 303 30 31, g32p_row21_traceSegment_042_0303_0030, g32p_row21_traceSegment_042_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_042 243 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 243 60 61, g32p_row21_traceSegment_042_0243_0060, g32p_row21_traceSegment_042_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 364 15 15, g32p_row21_traceSegment_042_0364_0015, g32p_row21_traceSegment_042_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 394 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 394 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 394 15 16, g32p_row21_traceSegment_042_0394_0015, g32p_row21_traceSegment_042_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 364 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 364 30 31, g32p_row21_traceSegment_042_0364_0030, g32p_row21_traceSegment_042_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 425 15 15, g32p_row21_traceSegment_042_0425_0015, g32p_row21_traceSegment_042_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 455 15 16, g32p_row21_traceSegment_042_0455_0015, g32p_row21_traceSegment_042_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 425 30 31, g32p_row21_traceSegment_042_0425_0030, g32p_row21_traceSegment_042_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_042 364 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 364 61 61, g32p_row21_traceSegment_042_0364_0061, g32p_row21_traceSegment_042_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_042 243 243 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 243 121 122, g32p_row21_traceSegment_042_0243_0121, g32p_row21_traceSegment_042_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_042 0 486 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 0 243 243, g32p_row21_traceSegment_042_0000_0243, g32p_row21_traceSegment_042_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 486 15 15, g32p_row21_traceSegment_042_0486_0015, g32p_row21_traceSegment_042_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 516 15 15, g32p_row21_traceSegment_042_0516_0015, g32p_row21_traceSegment_042_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_042 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 486 30 30, g32p_row21_traceSegment_042_0486_0030, g32p_row21_traceSegment_042_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 546 15 15, g32p_row21_traceSegment_042_0546_0015, g32p_row21_traceSegment_042_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 576 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 591 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 576 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 576 15 16, g32p_row21_traceSegment_042_0576_0015, g32p_row21_traceSegment_042_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 546 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 546 30 31, g32p_row21_traceSegment_042_0546_0030, g32p_row21_traceSegment_042_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_042 486 121 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 486 60 61, g32p_row21_traceSegment_042_0486_0060, g32p_row21_traceSegment_042_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 607 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 607 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 607 15 15, g32p_row21_traceSegment_042_0607_0015, g32p_row21_traceSegment_042_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 637 15 16, g32p_row21_traceSegment_042_0637_0015, g32p_row21_traceSegment_042_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 607 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 607 30 31, g32p_row21_traceSegment_042_0607_0030, g32p_row21_traceSegment_042_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 668 15 15, g32p_row21_traceSegment_042_0668_0015, g32p_row21_traceSegment_042_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 698 15 16, g32p_row21_traceSegment_042_0698_0015, g32p_row21_traceSegment_042_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 668 30 31, g32p_row21_traceSegment_042_0668_0030, g32p_row21_traceSegment_042_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_042 607 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 607 61 61, g32p_row21_traceSegment_042_0607_0061, g32p_row21_traceSegment_042_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_042 486 243 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 486 121 122, g32p_row21_traceSegment_042_0486_0121, g32p_row21_traceSegment_042_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 729 15 15, g32p_row21_traceSegment_042_0729_0015, g32p_row21_traceSegment_042_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 759 15 15, g32p_row21_traceSegment_042_0759_0015, g32p_row21_traceSegment_042_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_042 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 729 30 30, g32p_row21_traceSegment_042_0729_0030, g32p_row21_traceSegment_042_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 789 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 804 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 789 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 789 15 15, g32p_row21_traceSegment_042_0789_0015, g32p_row21_traceSegment_042_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 819 15 16, g32p_row21_traceSegment_042_0819_0015, g32p_row21_traceSegment_042_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 789 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 789 30 31, g32p_row21_traceSegment_042_0789_0030, g32p_row21_traceSegment_042_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_042 729 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 729 60 61, g32p_row21_traceSegment_042_0729_0060, g32p_row21_traceSegment_042_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 850 15 15, g32p_row21_traceSegment_042_0850_0015, g32p_row21_traceSegment_042_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 880 15 16, g32p_row21_traceSegment_042_0880_0015, g32p_row21_traceSegment_042_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 850 30 31, g32p_row21_traceSegment_042_0850_0030, g32p_row21_traceSegment_042_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_042 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 911 15 15, g32p_row21_traceSegment_042_0911_0015, g32p_row21_traceSegment_042_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_042 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_042 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_042_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_042 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 941 15 16, g32p_row21_traceSegment_042_0941_0015, g32p_row21_traceSegment_042_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_042 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 911 30 31, g32p_row21_traceSegment_042_0911_0030, g32p_row21_traceSegment_042_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_042 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 850 61 61, g32p_row21_traceSegment_042_0850_0061, g32p_row21_traceSegment_042_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_042 729 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 729 121 122, g32p_row21_traceSegment_042_0729_0121, g32p_row21_traceSegment_042_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_042 486 486 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 486 243 243, g32p_row21_traceSegment_042_0486_0243, g32p_row21_traceSegment_042_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_042_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_042 0 972 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_042 0 486 486, g32p_row21_traceSegment_042_0000_0486, g32p_row21_traceSegment_042_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_042 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 42 = [0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_042_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_043 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 43 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_043_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 0 15 15, g32p_row21_traceSegment_043_0000_0015, g32p_row21_traceSegment_043_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 30 15 15, g32p_row21_traceSegment_043_0030_0015, g32p_row21_traceSegment_043_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_043 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 0 30 30, g32p_row21_traceSegment_043_0000_0030, g32p_row21_traceSegment_043_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 60 15 15, g32p_row21_traceSegment_043_0060_0015, g32p_row21_traceSegment_043_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 90 15 16, g32p_row21_traceSegment_043_0090_0015, g32p_row21_traceSegment_043_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 60 30 31, g32p_row21_traceSegment_043_0060_0030, g32p_row21_traceSegment_043_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_043 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 0 60 61, g32p_row21_traceSegment_043_0000_0060, g32p_row21_traceSegment_043_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 121 15 15, g32p_row21_traceSegment_043_0121_0015, g32p_row21_traceSegment_043_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 151 15 16, g32p_row21_traceSegment_043_0151_0015, g32p_row21_traceSegment_043_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 121 30 31, g32p_row21_traceSegment_043_0121_0030, g32p_row21_traceSegment_043_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 182 15 15, g32p_row21_traceSegment_043_0182_0015, g32p_row21_traceSegment_043_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 212 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 227 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 212 31 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 212 15 16, g32p_row21_traceSegment_043_0212_0015, g32p_row21_traceSegment_043_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 182 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 182 30 31, g32p_row21_traceSegment_043_0182_0030, g32p_row21_traceSegment_043_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_043 121 122 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 121 61 61, g32p_row21_traceSegment_043_0121_0061, g32p_row21_traceSegment_043_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_043 0 243 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 0 121 122, g32p_row21_traceSegment_043_0000_0121, g32p_row21_traceSegment_043_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 243 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 243 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 243 15 15, g32p_row21_traceSegment_043_0243_0015, g32p_row21_traceSegment_043_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 273 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 273 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 273 15 15, g32p_row21_traceSegment_043_0273_0015, g32p_row21_traceSegment_043_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_043 243 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 243 30 30, g32p_row21_traceSegment_043_0243_0030, g32p_row21_traceSegment_043_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 303 15 15, g32p_row21_traceSegment_043_0303_0015, g32p_row21_traceSegment_043_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 333 15 16, g32p_row21_traceSegment_043_0333_0015, g32p_row21_traceSegment_043_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 303 30 31, g32p_row21_traceSegment_043_0303_0030, g32p_row21_traceSegment_043_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_043 243 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 243 60 61, g32p_row21_traceSegment_043_0243_0060, g32p_row21_traceSegment_043_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 364 15 15, g32p_row21_traceSegment_043_0364_0015, g32p_row21_traceSegment_043_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 394 15 16, g32p_row21_traceSegment_043_0394_0015, g32p_row21_traceSegment_043_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 364 30 31, g32p_row21_traceSegment_043_0364_0030, g32p_row21_traceSegment_043_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 440 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 425 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 425 15 15, g32p_row21_traceSegment_043_0425_0015, g32p_row21_traceSegment_043_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 455 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 470 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 455 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 455 15 16, g32p_row21_traceSegment_043_0455_0015, g32p_row21_traceSegment_043_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 425 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 425 30 31, g32p_row21_traceSegment_043_0425_0030, g32p_row21_traceSegment_043_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_043 364 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 364 61 61, g32p_row21_traceSegment_043_0364_0061, g32p_row21_traceSegment_043_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_043 243 243 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 243 121 122, g32p_row21_traceSegment_043_0243_0121, g32p_row21_traceSegment_043_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_043 0 486 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 0 243 243, g32p_row21_traceSegment_043_0000_0243, g32p_row21_traceSegment_043_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 501 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 486 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 486 15 15, g32p_row21_traceSegment_043_0486_0015, g32p_row21_traceSegment_043_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 516 15 15, g32p_row21_traceSegment_043_0516_0015, g32p_row21_traceSegment_043_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_043 486 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 486 30 30, g32p_row21_traceSegment_043_0486_0030, g32p_row21_traceSegment_043_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 546 15 15, g32p_row21_traceSegment_043_0546_0015, g32p_row21_traceSegment_043_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 576 15 16, g32p_row21_traceSegment_043_0576_0015, g32p_row21_traceSegment_043_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 546 30 31, g32p_row21_traceSegment_043_0546_0030, g32p_row21_traceSegment_043_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_043 486 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 486 60 61, g32p_row21_traceSegment_043_0486_0060, g32p_row21_traceSegment_043_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 607 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 622 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 607 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 607 15 15, g32p_row21_traceSegment_043_0607_0015, g32p_row21_traceSegment_043_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 637 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 637 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 637 15 16, g32p_row21_traceSegment_043_0637_0015, g32p_row21_traceSegment_043_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 607 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 607 30 31, g32p_row21_traceSegment_043_0607_0030, g32p_row21_traceSegment_043_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 668 15 15, g32p_row21_traceSegment_043_0668_0015, g32p_row21_traceSegment_043_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 698 15 16, g32p_row21_traceSegment_043_0698_0015, g32p_row21_traceSegment_043_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 668 30 31, g32p_row21_traceSegment_043_0668_0030, g32p_row21_traceSegment_043_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_043 607 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 607 61 61, g32p_row21_traceSegment_043_0607_0061, g32p_row21_traceSegment_043_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_043 486 243 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 486 121 122, g32p_row21_traceSegment_043_0486_0121, g32p_row21_traceSegment_043_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 729 15 15, g32p_row21_traceSegment_043_0729_0015, g32p_row21_traceSegment_043_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 759 15 15, g32p_row21_traceSegment_043_0759_0015, g32p_row21_traceSegment_043_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_043 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 729 30 30, g32p_row21_traceSegment_043_0729_0030, g32p_row21_traceSegment_043_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 789 15 15, g32p_row21_traceSegment_043_0789_0015, g32p_row21_traceSegment_043_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 819 15 16, g32p_row21_traceSegment_043_0819_0015, g32p_row21_traceSegment_043_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 789 30 31, g32p_row21_traceSegment_043_0789_0030, g32p_row21_traceSegment_043_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_043 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 729 60 61, g32p_row21_traceSegment_043_0729_0060, g32p_row21_traceSegment_043_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 850 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 865 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 850 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 850 15 15, g32p_row21_traceSegment_043_0850_0015, g32p_row21_traceSegment_043_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 880 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 880 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 880 15 16, g32p_row21_traceSegment_043_0880_0015, g32p_row21_traceSegment_043_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 850 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 850 30 31, g32p_row21_traceSegment_043_0850_0030, g32p_row21_traceSegment_043_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_043 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 911 15 15, g32p_row21_traceSegment_043_0911_0015, g32p_row21_traceSegment_043_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_043 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_043 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_043_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_043 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 941 15 16, g32p_row21_traceSegment_043_0941_0015, g32p_row21_traceSegment_043_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_043 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 911 30 31, g32p_row21_traceSegment_043_0911_0030, g32p_row21_traceSegment_043_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_043 850 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 850 61 61, g32p_row21_traceSegment_043_0850_0061, g32p_row21_traceSegment_043_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_043 729 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 729 121 122, g32p_row21_traceSegment_043_0729_0121, g32p_row21_traceSegment_043_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_043 486 486 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 486 243 243, g32p_row21_traceSegment_043_0486_0243, g32p_row21_traceSegment_043_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_043_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_043 0 972 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_043 0 486 486, g32p_row21_traceSegment_043_0000_0486, g32p_row21_traceSegment_043_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 43 = [0, 0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_043_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_044 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 44 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_044_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 0 15 15, g32p_row21_traceSegment_044_0000_0015, g32p_row21_traceSegment_044_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 30 15 15, g32p_row21_traceSegment_044_0030_0015, g32p_row21_traceSegment_044_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_044 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 0 30 30, g32p_row21_traceSegment_044_0000_0030, g32p_row21_traceSegment_044_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 60 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 60 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 60 15 15, g32p_row21_traceSegment_044_0060_0015, g32p_row21_traceSegment_044_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 90 15 16, g32p_row21_traceSegment_044_0090_0015, g32p_row21_traceSegment_044_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 60 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 60 30 31, g32p_row21_traceSegment_044_0060_0030, g32p_row21_traceSegment_044_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_044 0 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 0 60 61, g32p_row21_traceSegment_044_0000_0060, g32p_row21_traceSegment_044_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 121 15 15, g32p_row21_traceSegment_044_0121_0015, g32p_row21_traceSegment_044_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 151 15 16, g32p_row21_traceSegment_044_0151_0015, g32p_row21_traceSegment_044_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 121 30 31, g32p_row21_traceSegment_044_0121_0030, g32p_row21_traceSegment_044_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 182 15 15, g32p_row21_traceSegment_044_0182_0015, g32p_row21_traceSegment_044_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 212 15 16, g32p_row21_traceSegment_044_0212_0015, g32p_row21_traceSegment_044_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 182 30 31, g32p_row21_traceSegment_044_0182_0030, g32p_row21_traceSegment_044_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_044 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 121 61 61, g32p_row21_traceSegment_044_0121_0061, g32p_row21_traceSegment_044_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_044 0 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 0 121 122, g32p_row21_traceSegment_044_0000_0121, g32p_row21_traceSegment_044_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 243 15 15, g32p_row21_traceSegment_044_0243_0015, g32p_row21_traceSegment_044_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 273 15 15, g32p_row21_traceSegment_044_0273_0015, g32p_row21_traceSegment_044_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_044 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 243 30 30, g32p_row21_traceSegment_044_0243_0030, g32p_row21_traceSegment_044_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 303 15 15, g32p_row21_traceSegment_044_0303_0015, g32p_row21_traceSegment_044_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 333 15 16, g32p_row21_traceSegment_044_0333_0015, g32p_row21_traceSegment_044_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 303 30 31, g32p_row21_traceSegment_044_0303_0030, g32p_row21_traceSegment_044_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_044 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 243 60 61, g32p_row21_traceSegment_044_0243_0060, g32p_row21_traceSegment_044_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 364 15 15, g32p_row21_traceSegment_044_0364_0015, g32p_row21_traceSegment_044_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 394 15 16, g32p_row21_traceSegment_044_0394_0015, g32p_row21_traceSegment_044_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 364 30 31, g32p_row21_traceSegment_044_0364_0030, g32p_row21_traceSegment_044_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 425 15 15, g32p_row21_traceSegment_044_0425_0015, g32p_row21_traceSegment_044_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 455 15 16, g32p_row21_traceSegment_044_0455_0015, g32p_row21_traceSegment_044_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 425 30 31, g32p_row21_traceSegment_044_0425_0030, g32p_row21_traceSegment_044_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_044 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 364 61 61, g32p_row21_traceSegment_044_0364_0061, g32p_row21_traceSegment_044_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_044 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 243 121 122, g32p_row21_traceSegment_044_0243_0121, g32p_row21_traceSegment_044_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_044 0 486 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 0 243 243, g32p_row21_traceSegment_044_0000_0243, g32p_row21_traceSegment_044_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 486 15 15, g32p_row21_traceSegment_044_0486_0015, g32p_row21_traceSegment_044_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 516 15 15, g32p_row21_traceSegment_044_0516_0015, g32p_row21_traceSegment_044_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_044 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 486 30 30, g32p_row21_traceSegment_044_0486_0030, g32p_row21_traceSegment_044_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 546 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 561 15 = [1, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 546 30 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 546 15 15, g32p_row21_traceSegment_044_0546_0015, g32p_row21_traceSegment_044_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 576 15 16, g32p_row21_traceSegment_044_0576_0015, g32p_row21_traceSegment_044_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 546 61 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 546 30 31, g32p_row21_traceSegment_044_0546_0030, g32p_row21_traceSegment_044_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_044 486 121 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 486 60 61, g32p_row21_traceSegment_044_0486_0060, g32p_row21_traceSegment_044_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 607 15 15, g32p_row21_traceSegment_044_0607_0015, g32p_row21_traceSegment_044_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 637 15 16, g32p_row21_traceSegment_044_0637_0015, g32p_row21_traceSegment_044_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 607 30 31, g32p_row21_traceSegment_044_0607_0030, g32p_row21_traceSegment_044_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 668 15 15, g32p_row21_traceSegment_044_0668_0015, g32p_row21_traceSegment_044_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 698 15 16, g32p_row21_traceSegment_044_0698_0015, g32p_row21_traceSegment_044_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 668 30 31, g32p_row21_traceSegment_044_0668_0030, g32p_row21_traceSegment_044_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_044 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 607 61 61, g32p_row21_traceSegment_044_0607_0061, g32p_row21_traceSegment_044_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_044 486 243 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 486 121 122, g32p_row21_traceSegment_044_0486_0121, g32p_row21_traceSegment_044_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 729 15 15, g32p_row21_traceSegment_044_0729_0015, g32p_row21_traceSegment_044_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 759 15 15, g32p_row21_traceSegment_044_0759_0015, g32p_row21_traceSegment_044_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_044 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 729 30 30, g32p_row21_traceSegment_044_0729_0030, g32p_row21_traceSegment_044_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 789 15 15, g32p_row21_traceSegment_044_0789_0015, g32p_row21_traceSegment_044_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 819 15 16, g32p_row21_traceSegment_044_0819_0015, g32p_row21_traceSegment_044_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 789 30 31, g32p_row21_traceSegment_044_0789_0030, g32p_row21_traceSegment_044_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_044 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 729 60 61, g32p_row21_traceSegment_044_0729_0060, g32p_row21_traceSegment_044_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 850 15 15, g32p_row21_traceSegment_044_0850_0015, g32p_row21_traceSegment_044_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 880 15 16, g32p_row21_traceSegment_044_0880_0015, g32p_row21_traceSegment_044_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 850 30 31, g32p_row21_traceSegment_044_0850_0030, g32p_row21_traceSegment_044_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_044 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 911 15 15, g32p_row21_traceSegment_044_0911_0015, g32p_row21_traceSegment_044_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_044 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_044 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_044_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_044 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 941 15 16, g32p_row21_traceSegment_044_0941_0015, g32p_row21_traceSegment_044_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_044 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 911 30 31, g32p_row21_traceSegment_044_0911_0030, g32p_row21_traceSegment_044_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_044 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 850 61 61, g32p_row21_traceSegment_044_0850_0061, g32p_row21_traceSegment_044_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_044 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 729 121 122, g32p_row21_traceSegment_044_0729_0121, g32p_row21_traceSegment_044_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_044 486 486 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 486 243 243, g32p_row21_traceSegment_044_0486_0243, g32p_row21_traceSegment_044_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_044_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_044 0 972 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_044 0 486 486, g32p_row21_traceSegment_044_0000_0486, g32p_row21_traceSegment_044_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 44 = [1, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_044_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_045 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 45 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_045_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 0 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 0 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 0 15 15, g32p_row21_traceSegment_045_0000_0015, g32p_row21_traceSegment_045_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 30 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 45 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 30 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 30 15 15, g32p_row21_traceSegment_045_0030_0015, g32p_row21_traceSegment_045_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_045 0 60 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 0 30 30, g32p_row21_traceSegment_045_0000_0030, g32p_row21_traceSegment_045_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 75 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 60 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 60 15 15, g32p_row21_traceSegment_045_0060_0015, g32p_row21_traceSegment_045_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 90 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 90 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 90 15 16, g32p_row21_traceSegment_045_0090_0015, g32p_row21_traceSegment_045_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 60 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 60 30 31, g32p_row21_traceSegment_045_0060_0030, g32p_row21_traceSegment_045_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_045 0 121 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 0 60 61, g32p_row21_traceSegment_045_0000_0060, g32p_row21_traceSegment_045_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 121 15 15, g32p_row21_traceSegment_045_0121_0015, g32p_row21_traceSegment_045_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 151 15 16, g32p_row21_traceSegment_045_0151_0015, g32p_row21_traceSegment_045_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 121 30 31, g32p_row21_traceSegment_045_0121_0030, g32p_row21_traceSegment_045_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 197 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 182 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 182 15 15, g32p_row21_traceSegment_045_0182_0015, g32p_row21_traceSegment_045_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 212 15 16, g32p_row21_traceSegment_045_0212_0015, g32p_row21_traceSegment_045_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 182 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 182 30 31, g32p_row21_traceSegment_045_0182_0030, g32p_row21_traceSegment_045_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_045 121 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 121 61 61, g32p_row21_traceSegment_045_0121_0061, g32p_row21_traceSegment_045_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_045 0 243 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 0 121 122, g32p_row21_traceSegment_045_0000_0121, g32p_row21_traceSegment_045_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 243 15 15, g32p_row21_traceSegment_045_0243_0015, g32p_row21_traceSegment_045_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 273 15 15, g32p_row21_traceSegment_045_0273_0015, g32p_row21_traceSegment_045_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_045 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 243 30 30, g32p_row21_traceSegment_045_0243_0030, g32p_row21_traceSegment_045_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 318 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 303 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 303 15 15, g32p_row21_traceSegment_045_0303_0015, g32p_row21_traceSegment_045_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 333 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 348 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 333 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 333 15 16, g32p_row21_traceSegment_045_0333_0015, g32p_row21_traceSegment_045_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 303 61 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 303 30 31, g32p_row21_traceSegment_045_0303_0030, g32p_row21_traceSegment_045_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_045 243 121 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 243 60 61, g32p_row21_traceSegment_045_0243_0060, g32p_row21_traceSegment_045_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 364 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 364 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 364 15 15, g32p_row21_traceSegment_045_0364_0015, g32p_row21_traceSegment_045_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 394 15 16, g32p_row21_traceSegment_045_0394_0015, g32p_row21_traceSegment_045_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 364 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 364 30 31, g32p_row21_traceSegment_045_0364_0030, g32p_row21_traceSegment_045_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 425 15 15, g32p_row21_traceSegment_045_0425_0015, g32p_row21_traceSegment_045_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 455 15 16, g32p_row21_traceSegment_045_0455_0015, g32p_row21_traceSegment_045_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 425 30 31, g32p_row21_traceSegment_045_0425_0030, g32p_row21_traceSegment_045_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_045 364 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 364 61 61, g32p_row21_traceSegment_045_0364_0061, g32p_row21_traceSegment_045_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_045 243 243 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 243 121 122, g32p_row21_traceSegment_045_0243_0121, g32p_row21_traceSegment_045_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_045 0 486 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 0 243 243, g32p_row21_traceSegment_045_0000_0243, g32p_row21_traceSegment_045_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 486 15 15, g32p_row21_traceSegment_045_0486_0015, g32p_row21_traceSegment_045_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 516 15 15, g32p_row21_traceSegment_045_0516_0015, g32p_row21_traceSegment_045_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_045 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 486 30 30, g32p_row21_traceSegment_045_0486_0030, g32p_row21_traceSegment_045_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 561 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 546 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 546 15 15, g32p_row21_traceSegment_045_0546_0015, g32p_row21_traceSegment_045_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 576 15 16, g32p_row21_traceSegment_045_0576_0015, g32p_row21_traceSegment_045_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 546 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 546 30 31, g32p_row21_traceSegment_045_0546_0030, g32p_row21_traceSegment_045_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_045 486 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 486 60 61, g32p_row21_traceSegment_045_0486_0060, g32p_row21_traceSegment_045_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 607 15 15, g32p_row21_traceSegment_045_0607_0015, g32p_row21_traceSegment_045_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 637 15 16, g32p_row21_traceSegment_045_0637_0015, g32p_row21_traceSegment_045_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 607 30 31, g32p_row21_traceSegment_045_0607_0030, g32p_row21_traceSegment_045_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 683 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 668 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 668 15 15, g32p_row21_traceSegment_045_0668_0015, g32p_row21_traceSegment_045_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 713 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 698 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 698 15 16, g32p_row21_traceSegment_045_0698_0015, g32p_row21_traceSegment_045_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 668 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 668 30 31, g32p_row21_traceSegment_045_0668_0030, g32p_row21_traceSegment_045_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_045 607 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 607 61 61, g32p_row21_traceSegment_045_0607_0061, g32p_row21_traceSegment_045_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_045 486 243 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 486 121 122, g32p_row21_traceSegment_045_0486_0121, g32p_row21_traceSegment_045_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 729 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 744 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 729 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 729 15 15, g32p_row21_traceSegment_045_0729_0015, g32p_row21_traceSegment_045_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 774 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 759 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 759 15 15, g32p_row21_traceSegment_045_0759_0015, g32p_row21_traceSegment_045_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_045 729 60 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 729 30 30, g32p_row21_traceSegment_045_0729_0030, g32p_row21_traceSegment_045_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 789 15 = [1, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 804 15 = [1, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 789 30 = [2, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 789 15 15, g32p_row21_traceSegment_045_0789_0015, g32p_row21_traceSegment_045_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 819 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 834 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 819 31 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 819 15 16, g32p_row21_traceSegment_045_0819_0015, g32p_row21_traceSegment_045_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 789 61 = [3, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 789 30 31, g32p_row21_traceSegment_045_0789_0030, g32p_row21_traceSegment_045_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_045 729 121 = [3, 8, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 729 60 61, g32p_row21_traceSegment_045_0729_0060, g32p_row21_traceSegment_045_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 850 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 850 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 850 15 15, g32p_row21_traceSegment_045_0850_0015, g32p_row21_traceSegment_045_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 880 15 16, g32p_row21_traceSegment_045_0880_0015, g32p_row21_traceSegment_045_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 850 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 850 30 31, g32p_row21_traceSegment_045_0850_0030, g32p_row21_traceSegment_045_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_045 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 911 15 15, g32p_row21_traceSegment_045_0911_0015, g32p_row21_traceSegment_045_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_045 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_045 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_045_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_045 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 941 15 16, g32p_row21_traceSegment_045_0941_0015, g32p_row21_traceSegment_045_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_045 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 911 30 31, g32p_row21_traceSegment_045_0911_0030, g32p_row21_traceSegment_045_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_045 850 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 850 61 61, g32p_row21_traceSegment_045_0850_0061, g32p_row21_traceSegment_045_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_045 729 243 = [3, 8, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 729 121 122, g32p_row21_traceSegment_045_0729_0121, g32p_row21_traceSegment_045_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_045 486 486 = [3, 11, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 486 243 243, g32p_row21_traceSegment_045_0486_0243, g32p_row21_traceSegment_045_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_045_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_045 0 972 = [3, 24, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_045 0 486 486, g32p_row21_traceSegment_045_0000_0486, g32p_row21_traceSegment_045_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 45 = [3, 24, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_045_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_050 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 50 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_050_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 0 15 15, g32p_row21_traceSegment_050_0000_0015, g32p_row21_traceSegment_050_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 30 15 15, g32p_row21_traceSegment_050_0030_0015, g32p_row21_traceSegment_050_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_050 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 0 30 30, g32p_row21_traceSegment_050_0000_0030, g32p_row21_traceSegment_050_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 60 15 15, g32p_row21_traceSegment_050_0060_0015, g32p_row21_traceSegment_050_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 90 15 16, g32p_row21_traceSegment_050_0090_0015, g32p_row21_traceSegment_050_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 60 30 31, g32p_row21_traceSegment_050_0060_0030, g32p_row21_traceSegment_050_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_050 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 0 60 61, g32p_row21_traceSegment_050_0000_0060, g32p_row21_traceSegment_050_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 121 15 15, g32p_row21_traceSegment_050_0121_0015, g32p_row21_traceSegment_050_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 151 15 16, g32p_row21_traceSegment_050_0151_0015, g32p_row21_traceSegment_050_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 121 30 31, g32p_row21_traceSegment_050_0121_0030, g32p_row21_traceSegment_050_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 182 15 15, g32p_row21_traceSegment_050_0182_0015, g32p_row21_traceSegment_050_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 212 15 16, g32p_row21_traceSegment_050_0212_0015, g32p_row21_traceSegment_050_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 182 30 31, g32p_row21_traceSegment_050_0182_0030, g32p_row21_traceSegment_050_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_050 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 121 61 61, g32p_row21_traceSegment_050_0121_0061, g32p_row21_traceSegment_050_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_050 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 0 121 122, g32p_row21_traceSegment_050_0000_0121, g32p_row21_traceSegment_050_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 243 15 15, g32p_row21_traceSegment_050_0243_0015, g32p_row21_traceSegment_050_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 273 15 15, g32p_row21_traceSegment_050_0273_0015, g32p_row21_traceSegment_050_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_050 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 243 30 30, g32p_row21_traceSegment_050_0243_0030, g32p_row21_traceSegment_050_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 303 15 15, g32p_row21_traceSegment_050_0303_0015, g32p_row21_traceSegment_050_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 333 15 16, g32p_row21_traceSegment_050_0333_0015, g32p_row21_traceSegment_050_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 303 30 31, g32p_row21_traceSegment_050_0303_0030, g32p_row21_traceSegment_050_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_050 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 243 60 61, g32p_row21_traceSegment_050_0243_0060, g32p_row21_traceSegment_050_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 364 15 15, g32p_row21_traceSegment_050_0364_0015, g32p_row21_traceSegment_050_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 409 16 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 394 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 394 15 16, g32p_row21_traceSegment_050_0394_0015, g32p_row21_traceSegment_050_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 364 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 364 30 31, g32p_row21_traceSegment_050_0364_0030, g32p_row21_traceSegment_050_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 440 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 425 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 425 15 15, g32p_row21_traceSegment_050_0425_0015, g32p_row21_traceSegment_050_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 455 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 470 16 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 455 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 455 15 16, g32p_row21_traceSegment_050_0455_0015, g32p_row21_traceSegment_050_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 425 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 425 30 31, g32p_row21_traceSegment_050_0425_0030, g32p_row21_traceSegment_050_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_050 364 122 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 364 61 61, g32p_row21_traceSegment_050_0364_0061, g32p_row21_traceSegment_050_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_050 243 243 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 243 121 122, g32p_row21_traceSegment_050_0243_0121, g32p_row21_traceSegment_050_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_050 0 486 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 0 243 243, g32p_row21_traceSegment_050_0000_0243, g32p_row21_traceSegment_050_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 486 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 501 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 486 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 486 15 15, g32p_row21_traceSegment_050_0486_0015, g32p_row21_traceSegment_050_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 516 15 15, g32p_row21_traceSegment_050_0516_0015, g32p_row21_traceSegment_050_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_050 486 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 486 30 30, g32p_row21_traceSegment_050_0486_0030, g32p_row21_traceSegment_050_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 546 15 15, g32p_row21_traceSegment_050_0546_0015, g32p_row21_traceSegment_050_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 576 15 16, g32p_row21_traceSegment_050_0576_0015, g32p_row21_traceSegment_050_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 546 30 31, g32p_row21_traceSegment_050_0546_0030, g32p_row21_traceSegment_050_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_050 486 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 486 60 61, g32p_row21_traceSegment_050_0486_0060, g32p_row21_traceSegment_050_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 607 15 15, g32p_row21_traceSegment_050_0607_0015, g32p_row21_traceSegment_050_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 637 15 16, g32p_row21_traceSegment_050_0637_0015, g32p_row21_traceSegment_050_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 607 30 31, g32p_row21_traceSegment_050_0607_0030, g32p_row21_traceSegment_050_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 683 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 668 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 668 15 15, g32p_row21_traceSegment_050_0668_0015, g32p_row21_traceSegment_050_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 713 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 698 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 698 15 16, g32p_row21_traceSegment_050_0698_0015, g32p_row21_traceSegment_050_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 668 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 668 30 31, g32p_row21_traceSegment_050_0668_0030, g32p_row21_traceSegment_050_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_050 607 122 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 607 61 61, g32p_row21_traceSegment_050_0607_0061, g32p_row21_traceSegment_050_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_050 486 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 486 121 122, g32p_row21_traceSegment_050_0486_0121, g32p_row21_traceSegment_050_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 729 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 744 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 729 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 729 15 15, g32p_row21_traceSegment_050_0729_0015, g32p_row21_traceSegment_050_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 759 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 759 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 759 15 15, g32p_row21_traceSegment_050_0759_0015, g32p_row21_traceSegment_050_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_050 729 60 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 729 30 30, g32p_row21_traceSegment_050_0729_0030, g32p_row21_traceSegment_050_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 789 15 15, g32p_row21_traceSegment_050_0789_0015, g32p_row21_traceSegment_050_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 819 15 16, g32p_row21_traceSegment_050_0819_0015, g32p_row21_traceSegment_050_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 789 30 31, g32p_row21_traceSegment_050_0789_0030, g32p_row21_traceSegment_050_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_050 729 121 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 729 60 61, g32p_row21_traceSegment_050_0729_0060, g32p_row21_traceSegment_050_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 850 15 15, g32p_row21_traceSegment_050_0850_0015, g32p_row21_traceSegment_050_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 880 15 16, g32p_row21_traceSegment_050_0880_0015, g32p_row21_traceSegment_050_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 850 30 31, g32p_row21_traceSegment_050_0850_0030, g32p_row21_traceSegment_050_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_050 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 911 15 15, g32p_row21_traceSegment_050_0911_0015, g32p_row21_traceSegment_050_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_050 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_050 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_050_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_050 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 941 15 16, g32p_row21_traceSegment_050_0941_0015, g32p_row21_traceSegment_050_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_050 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 911 30 31, g32p_row21_traceSegment_050_0911_0030, g32p_row21_traceSegment_050_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_050 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 850 61 61, g32p_row21_traceSegment_050_0850_0061, g32p_row21_traceSegment_050_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_050 729 243 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 729 121 122, g32p_row21_traceSegment_050_0729_0121, g32p_row21_traceSegment_050_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_050 486 486 = [11] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 486 243 243, g32p_row21_traceSegment_050_0486_0243, g32p_row21_traceSegment_050_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_050_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_050 0 972 = [18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_050 0 486 486, g32p_row21_traceSegment_050_0000_0486, g32p_row21_traceSegment_050_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 50 = [18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_050_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row21_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 37) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 37) (g32p_literalTraceValue 20 37)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row21_traceCoefficients_037]
  decide +kernel

theorem g32p_row21_tracePolynomial_039 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 39) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 39) (g32p_literalTraceValue 20 39)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_039]
  decide +kernel

theorem g32p_row21_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 40) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 40) (g32p_literalTraceValue 20 40)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_040]
  decide +kernel

theorem g32p_row21_tracePolynomial_042 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 42) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 42) (g32p_literalTraceValue 20 42)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_042]
  decide +kernel

theorem g32p_row21_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 43) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 43) (g32p_literalTraceValue 20 43)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row21_traceCoefficients_043]
  decide +kernel

theorem g32p_row21_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 44) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 44) (g32p_literalTraceValue 20 44)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_044]
  decide +kernel

theorem g32p_row21_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 45) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 45) (g32p_literalTraceValue 20 45)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_045]
  decide +kernel

theorem g32p_row21_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 50) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 50) (g32p_literalTraceValue 20 50)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_050]
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

private def g32p_row21_traceSegment_051 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 51 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_051_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 15 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 0 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 0 15 15, g32p_row21_traceSegment_051_0000_0015, g32p_row21_traceSegment_051_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 30 15 15, g32p_row21_traceSegment_051_0030_0015, g32p_row21_traceSegment_051_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_051 0 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 0 30 30, g32p_row21_traceSegment_051_0000_0030, g32p_row21_traceSegment_051_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 60 15 15, g32p_row21_traceSegment_051_0060_0015, g32p_row21_traceSegment_051_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 90 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 90 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 90 15 16, g32p_row21_traceSegment_051_0090_0015, g32p_row21_traceSegment_051_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 60 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 60 30 31, g32p_row21_traceSegment_051_0060_0030, g32p_row21_traceSegment_051_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_051 0 121 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 0 60 61, g32p_row21_traceSegment_051_0000_0060, g32p_row21_traceSegment_051_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 121 15 15, g32p_row21_traceSegment_051_0121_0015, g32p_row21_traceSegment_051_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 151 15 16, g32p_row21_traceSegment_051_0151_0015, g32p_row21_traceSegment_051_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 121 30 31, g32p_row21_traceSegment_051_0121_0030, g32p_row21_traceSegment_051_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 197 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 182 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 182 15 15, g32p_row21_traceSegment_051_0182_0015, g32p_row21_traceSegment_051_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 212 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 227 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 212 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 212 15 16, g32p_row21_traceSegment_051_0212_0015, g32p_row21_traceSegment_051_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 182 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 182 30 31, g32p_row21_traceSegment_051_0182_0030, g32p_row21_traceSegment_051_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_051 121 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 121 61 61, g32p_row21_traceSegment_051_0121_0061, g32p_row21_traceSegment_051_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_051 0 243 = [1, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 0 121 122, g32p_row21_traceSegment_051_0000_0121, g32p_row21_traceSegment_051_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 258 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 243 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 243 15 15, g32p_row21_traceSegment_051_0243_0015, g32p_row21_traceSegment_051_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 273 15 15, g32p_row21_traceSegment_051_0273_0015, g32p_row21_traceSegment_051_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_051 243 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 243 30 30, g32p_row21_traceSegment_051_0243_0030, g32p_row21_traceSegment_051_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 303 15 15, g32p_row21_traceSegment_051_0303_0015, g32p_row21_traceSegment_051_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 333 15 16, g32p_row21_traceSegment_051_0333_0015, g32p_row21_traceSegment_051_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 303 30 31, g32p_row21_traceSegment_051_0303_0030, g32p_row21_traceSegment_051_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_051 243 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 243 60 61, g32p_row21_traceSegment_051_0243_0060, g32p_row21_traceSegment_051_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 364 15 15, g32p_row21_traceSegment_051_0364_0015, g32p_row21_traceSegment_051_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 394 15 16, g32p_row21_traceSegment_051_0394_0015, g32p_row21_traceSegment_051_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 364 30 31, g32p_row21_traceSegment_051_0364_0030, g32p_row21_traceSegment_051_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 425 15 15, g32p_row21_traceSegment_051_0425_0015, g32p_row21_traceSegment_051_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 455 15 16, g32p_row21_traceSegment_051_0455_0015, g32p_row21_traceSegment_051_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 425 30 31, g32p_row21_traceSegment_051_0425_0030, g32p_row21_traceSegment_051_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_051 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 364 61 61, g32p_row21_traceSegment_051_0364_0061, g32p_row21_traceSegment_051_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_051 243 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 243 121 122, g32p_row21_traceSegment_051_0243_0121, g32p_row21_traceSegment_051_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_051 0 486 = [1, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 0 243 243, g32p_row21_traceSegment_051_0000_0243, g32p_row21_traceSegment_051_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 486 15 15, g32p_row21_traceSegment_051_0486_0015, g32p_row21_traceSegment_051_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 516 15 15, g32p_row21_traceSegment_051_0516_0015, g32p_row21_traceSegment_051_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_051 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 486 30 30, g32p_row21_traceSegment_051_0486_0030, g32p_row21_traceSegment_051_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 546 15 15, g32p_row21_traceSegment_051_0546_0015, g32p_row21_traceSegment_051_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 576 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 576 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 576 15 16, g32p_row21_traceSegment_051_0576_0015, g32p_row21_traceSegment_051_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 546 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 546 30 31, g32p_row21_traceSegment_051_0546_0030, g32p_row21_traceSegment_051_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_051 486 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 486 60 61, g32p_row21_traceSegment_051_0486_0060, g32p_row21_traceSegment_051_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 607 15 15, g32p_row21_traceSegment_051_0607_0015, g32p_row21_traceSegment_051_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 637 15 16, g32p_row21_traceSegment_051_0637_0015, g32p_row21_traceSegment_051_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 607 30 31, g32p_row21_traceSegment_051_0607_0030, g32p_row21_traceSegment_051_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 668 15 15, g32p_row21_traceSegment_051_0668_0015, g32p_row21_traceSegment_051_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 698 15 16, g32p_row21_traceSegment_051_0698_0015, g32p_row21_traceSegment_051_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 668 30 31, g32p_row21_traceSegment_051_0668_0030, g32p_row21_traceSegment_051_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_051 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 607 61 61, g32p_row21_traceSegment_051_0607_0061, g32p_row21_traceSegment_051_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_051 486 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 486 121 122, g32p_row21_traceSegment_051_0486_0121, g32p_row21_traceSegment_051_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 744 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 729 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 729 15 15, g32p_row21_traceSegment_051_0729_0015, g32p_row21_traceSegment_051_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 759 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 774 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 759 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 759 15 15, g32p_row21_traceSegment_051_0759_0015, g32p_row21_traceSegment_051_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_051 729 60 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 729 30 30, g32p_row21_traceSegment_051_0729_0030, g32p_row21_traceSegment_051_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 789 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 804 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 789 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 789 15 15, g32p_row21_traceSegment_051_0789_0015, g32p_row21_traceSegment_051_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 819 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 819 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 819 15 16, g32p_row21_traceSegment_051_0819_0015, g32p_row21_traceSegment_051_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 789 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 789 30 31, g32p_row21_traceSegment_051_0789_0030, g32p_row21_traceSegment_051_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_051 729 121 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 729 60 61, g32p_row21_traceSegment_051_0729_0060, g32p_row21_traceSegment_051_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 850 15 15, g32p_row21_traceSegment_051_0850_0015, g32p_row21_traceSegment_051_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 880 15 16, g32p_row21_traceSegment_051_0880_0015, g32p_row21_traceSegment_051_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 850 30 31, g32p_row21_traceSegment_051_0850_0030, g32p_row21_traceSegment_051_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 926 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_051 911 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 911 15 15, g32p_row21_traceSegment_051_0911_0015, g32p_row21_traceSegment_051_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_051 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_051 956 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_051_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_051 941 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 941 15 16, g32p_row21_traceSegment_051_0941_0015, g32p_row21_traceSegment_051_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_051 911 61 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 911 30 31, g32p_row21_traceSegment_051_0911_0030, g32p_row21_traceSegment_051_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_051 850 122 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 850 61 61, g32p_row21_traceSegment_051_0850_0061, g32p_row21_traceSegment_051_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_051 729 243 = [8, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 729 121 122, g32p_row21_traceSegment_051_0729_0121, g32p_row21_traceSegment_051_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_051 486 486 = [8, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 486 243 243, g32p_row21_traceSegment_051_0486_0243, g32p_row21_traceSegment_051_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_051_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_051 0 972 = [9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_051 0 486 486, g32p_row21_traceSegment_051_0000_0486, g32p_row21_traceSegment_051_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 51 = [9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_051_0000_0972

end HodgeLean.Foundations.Program

end
end
