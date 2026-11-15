import HodgeLean.Foundations.Program.G32PropFourSixPacked0382
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_006 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 6 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_006_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 0 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 0 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 0 15 15, g32p_row21_traceSegment_006_0000_0015, g32p_row21_traceSegment_006_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 30 15 15, g32p_row21_traceSegment_006_0030_0015, g32p_row21_traceSegment_006_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_006 0 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 0 30 30, g32p_row21_traceSegment_006_0000_0030, g32p_row21_traceSegment_006_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 60 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 75 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 60 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 60 15 15, g32p_row21_traceSegment_006_0060_0015, g32p_row21_traceSegment_006_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 90 15 16, g32p_row21_traceSegment_006_0090_0015, g32p_row21_traceSegment_006_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 60 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 60 30 31, g32p_row21_traceSegment_006_0060_0030, g32p_row21_traceSegment_006_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_006 0 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 0 60 61, g32p_row21_traceSegment_006_0000_0060, g32p_row21_traceSegment_006_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 121 15 15, g32p_row21_traceSegment_006_0121_0015, g32p_row21_traceSegment_006_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 151 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 151 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 151 15 16, g32p_row21_traceSegment_006_0151_0015, g32p_row21_traceSegment_006_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 121 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 121 30 31, g32p_row21_traceSegment_006_0121_0030, g32p_row21_traceSegment_006_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 182 15 15, g32p_row21_traceSegment_006_0182_0015, g32p_row21_traceSegment_006_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 212 15 16, g32p_row21_traceSegment_006_0212_0015, g32p_row21_traceSegment_006_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 182 30 31, g32p_row21_traceSegment_006_0182_0030, g32p_row21_traceSegment_006_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_006 121 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 121 61 61, g32p_row21_traceSegment_006_0121_0061, g32p_row21_traceSegment_006_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_006 0 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 0 121 122, g32p_row21_traceSegment_006_0000_0121, g32p_row21_traceSegment_006_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 258 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 243 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 243 15 15, g32p_row21_traceSegment_006_0243_0015, g32p_row21_traceSegment_006_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 273 15 15, g32p_row21_traceSegment_006_0273_0015, g32p_row21_traceSegment_006_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_006 243 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 243 30 30, g32p_row21_traceSegment_006_0243_0030, g32p_row21_traceSegment_006_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 318 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 303 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 303 15 15, g32p_row21_traceSegment_006_0303_0015, g32p_row21_traceSegment_006_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 333 15 16, g32p_row21_traceSegment_006_0333_0015, g32p_row21_traceSegment_006_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 303 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 303 30 31, g32p_row21_traceSegment_006_0303_0030, g32p_row21_traceSegment_006_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_006 243 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 243 60 61, g32p_row21_traceSegment_006_0243_0060, g32p_row21_traceSegment_006_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 364 15 15, g32p_row21_traceSegment_006_0364_0015, g32p_row21_traceSegment_006_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 394 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 409 16 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 394 31 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 394 15 16, g32p_row21_traceSegment_006_0394_0015, g32p_row21_traceSegment_006_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 364 61 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 364 30 31, g32p_row21_traceSegment_006_0364_0030, g32p_row21_traceSegment_006_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 425 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 440 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 425 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 425 15 15, g32p_row21_traceSegment_006_0425_0015, g32p_row21_traceSegment_006_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 455 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 470 16 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 455 31 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 455 15 16, g32p_row21_traceSegment_006_0455_0015, g32p_row21_traceSegment_006_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 425 61 = [4, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 425 30 31, g32p_row21_traceSegment_006_0425_0030, g32p_row21_traceSegment_006_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_006 364 122 = [6, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 364 61 61, g32p_row21_traceSegment_006_0364_0061, g32p_row21_traceSegment_006_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_006 243 243 = [9, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 243 121 122, g32p_row21_traceSegment_006_0243_0121, g32p_row21_traceSegment_006_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_006 0 486 = [14, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 0 243 243, g32p_row21_traceSegment_006_0000_0243, g32p_row21_traceSegment_006_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 501 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 486 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 486 15 15, g32p_row21_traceSegment_006_0486_0015, g32p_row21_traceSegment_006_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 516 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 531 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 516 30 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 516 15 15, g32p_row21_traceSegment_006_0516_0015, g32p_row21_traceSegment_006_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_006 486 60 = [4, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 486 30 30, g32p_row21_traceSegment_006_0486_0030, g32p_row21_traceSegment_006_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 546 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 546 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 546 15 15, g32p_row21_traceSegment_006_0546_0015, g32p_row21_traceSegment_006_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 576 15 16, g32p_row21_traceSegment_006_0576_0015, g32p_row21_traceSegment_006_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 546 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 546 30 31, g32p_row21_traceSegment_006_0546_0030, g32p_row21_traceSegment_006_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_006 486 121 = [6, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 486 60 61, g32p_row21_traceSegment_006_0486_0060, g32p_row21_traceSegment_006_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 607 15 15, g32p_row21_traceSegment_006_0607_0015, g32p_row21_traceSegment_006_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 637 15 16, g32p_row21_traceSegment_006_0637_0015, g32p_row21_traceSegment_006_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 607 30 31, g32p_row21_traceSegment_006_0607_0030, g32p_row21_traceSegment_006_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 668 15 15, g32p_row21_traceSegment_006_0668_0015, g32p_row21_traceSegment_006_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 713 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 698 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 698 15 16, g32p_row21_traceSegment_006_0698_0015, g32p_row21_traceSegment_006_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 668 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 668 30 31, g32p_row21_traceSegment_006_0668_0030, g32p_row21_traceSegment_006_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_006 607 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 607 61 61, g32p_row21_traceSegment_006_0607_0061, g32p_row21_traceSegment_006_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_006 486 243 = [6, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 486 121 122, g32p_row21_traceSegment_006_0486_0121, g32p_row21_traceSegment_006_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 744 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 729 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 729 15 15, g32p_row21_traceSegment_006_0729_0015, g32p_row21_traceSegment_006_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 759 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 759 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 759 15 15, g32p_row21_traceSegment_006_0759_0015, g32p_row21_traceSegment_006_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_006 729 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 729 30 30, g32p_row21_traceSegment_006_0729_0030, g32p_row21_traceSegment_006_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 789 15 15, g32p_row21_traceSegment_006_0789_0015, g32p_row21_traceSegment_006_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 834 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 819 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 819 15 16, g32p_row21_traceSegment_006_0819_0015, g32p_row21_traceSegment_006_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 789 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 789 30 31, g32p_row21_traceSegment_006_0789_0030, g32p_row21_traceSegment_006_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_006 729 121 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 729 60 61, g32p_row21_traceSegment_006_0729_0060, g32p_row21_traceSegment_006_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 850 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 865 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 850 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 850 15 15, g32p_row21_traceSegment_006_0850_0015, g32p_row21_traceSegment_006_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 880 15 16, g32p_row21_traceSegment_006_0880_0015, g32p_row21_traceSegment_006_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 850 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 850 30 31, g32p_row21_traceSegment_006_0850_0030, g32p_row21_traceSegment_006_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_006 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 911 15 15, g32p_row21_traceSegment_006_0911_0015, g32p_row21_traceSegment_006_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_006 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_006 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_006_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_006 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 941 15 16, g32p_row21_traceSegment_006_0941_0015, g32p_row21_traceSegment_006_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_006 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 911 30 31, g32p_row21_traceSegment_006_0911_0030, g32p_row21_traceSegment_006_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_006 850 122 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 850 61 61, g32p_row21_traceSegment_006_0850_0061, g32p_row21_traceSegment_006_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_006 729 243 = [4, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 729 121 122, g32p_row21_traceSegment_006_0729_0121, g32p_row21_traceSegment_006_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_006 486 486 = [10, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 486 243 243, g32p_row21_traceSegment_006_0486_0243, g32p_row21_traceSegment_006_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_006_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_006 0 972 = [24, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_006 0 486 486, g32p_row21_traceSegment_006_0000_0486, g32p_row21_traceSegment_006_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 6 = [24, 3, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_006_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_008 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 8 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_008_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 15 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 0 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 0 15 15, g32p_row21_traceSegment_008_0000_0015, g32p_row21_traceSegment_008_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 30 15 15, g32p_row21_traceSegment_008_0030_0015, g32p_row21_traceSegment_008_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_008 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 0 30 30, g32p_row21_traceSegment_008_0000_0030, g32p_row21_traceSegment_008_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 60 15 15, g32p_row21_traceSegment_008_0060_0015, g32p_row21_traceSegment_008_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 90 15 16, g32p_row21_traceSegment_008_0090_0015, g32p_row21_traceSegment_008_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 60 30 31, g32p_row21_traceSegment_008_0060_0030, g32p_row21_traceSegment_008_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_008 0 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 0 60 61, g32p_row21_traceSegment_008_0000_0060, g32p_row21_traceSegment_008_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 136 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 121 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 121 15 15, g32p_row21_traceSegment_008_0121_0015, g32p_row21_traceSegment_008_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 151 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 151 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 151 15 16, g32p_row21_traceSegment_008_0151_0015, g32p_row21_traceSegment_008_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 121 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 121 30 31, g32p_row21_traceSegment_008_0121_0030, g32p_row21_traceSegment_008_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 182 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 197 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 182 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 182 15 15, g32p_row21_traceSegment_008_0182_0015, g32p_row21_traceSegment_008_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 212 15 16, g32p_row21_traceSegment_008_0212_0015, g32p_row21_traceSegment_008_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 182 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 182 30 31, g32p_row21_traceSegment_008_0182_0030, g32p_row21_traceSegment_008_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_008 121 122 = [0, 3, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 121 61 61, g32p_row21_traceSegment_008_0121_0061, g32p_row21_traceSegment_008_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_008 0 243 = [0, 3, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 0 121 122, g32p_row21_traceSegment_008_0000_0121, g32p_row21_traceSegment_008_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 243 15 15, g32p_row21_traceSegment_008_0243_0015, g32p_row21_traceSegment_008_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 273 15 15, g32p_row21_traceSegment_008_0273_0015, g32p_row21_traceSegment_008_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_008 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 243 30 30, g32p_row21_traceSegment_008_0243_0030, g32p_row21_traceSegment_008_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 303 15 15, g32p_row21_traceSegment_008_0303_0015, g32p_row21_traceSegment_008_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 333 15 16, g32p_row21_traceSegment_008_0333_0015, g32p_row21_traceSegment_008_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 303 30 31, g32p_row21_traceSegment_008_0303_0030, g32p_row21_traceSegment_008_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_008 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 243 60 61, g32p_row21_traceSegment_008_0243_0060, g32p_row21_traceSegment_008_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 364 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 379 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 364 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 364 15 15, g32p_row21_traceSegment_008_0364_0015, g32p_row21_traceSegment_008_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 394 15 16, g32p_row21_traceSegment_008_0394_0015, g32p_row21_traceSegment_008_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 364 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 364 30 31, g32p_row21_traceSegment_008_0364_0030, g32p_row21_traceSegment_008_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 425 15 15, g32p_row21_traceSegment_008_0425_0015, g32p_row21_traceSegment_008_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 455 15 16, g32p_row21_traceSegment_008_0455_0015, g32p_row21_traceSegment_008_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 425 30 31, g32p_row21_traceSegment_008_0425_0030, g32p_row21_traceSegment_008_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_008 364 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 364 61 61, g32p_row21_traceSegment_008_0364_0061, g32p_row21_traceSegment_008_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_008 243 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 243 121 122, g32p_row21_traceSegment_008_0243_0121, g32p_row21_traceSegment_008_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_008 0 486 = [0, 3, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 0 243 243, g32p_row21_traceSegment_008_0000_0243, g32p_row21_traceSegment_008_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 486 15 15, g32p_row21_traceSegment_008_0486_0015, g32p_row21_traceSegment_008_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 516 15 15, g32p_row21_traceSegment_008_0516_0015, g32p_row21_traceSegment_008_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_008 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 486 30 30, g32p_row21_traceSegment_008_0486_0030, g32p_row21_traceSegment_008_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 546 15 15, g32p_row21_traceSegment_008_0546_0015, g32p_row21_traceSegment_008_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 576 15 16, g32p_row21_traceSegment_008_0576_0015, g32p_row21_traceSegment_008_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 546 30 31, g32p_row21_traceSegment_008_0546_0030, g32p_row21_traceSegment_008_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_008 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 486 60 61, g32p_row21_traceSegment_008_0486_0060, g32p_row21_traceSegment_008_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 607 15 15, g32p_row21_traceSegment_008_0607_0015, g32p_row21_traceSegment_008_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 637 15 16, g32p_row21_traceSegment_008_0637_0015, g32p_row21_traceSegment_008_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 607 30 31, g32p_row21_traceSegment_008_0607_0030, g32p_row21_traceSegment_008_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 668 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 668 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 668 15 15, g32p_row21_traceSegment_008_0668_0015, g32p_row21_traceSegment_008_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 698 15 16, g32p_row21_traceSegment_008_0698_0015, g32p_row21_traceSegment_008_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 668 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 668 30 31, g32p_row21_traceSegment_008_0668_0030, g32p_row21_traceSegment_008_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_008 607 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 607 61 61, g32p_row21_traceSegment_008_0607_0061, g32p_row21_traceSegment_008_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_008 486 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 486 121 122, g32p_row21_traceSegment_008_0486_0121, g32p_row21_traceSegment_008_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 729 15 15, g32p_row21_traceSegment_008_0729_0015, g32p_row21_traceSegment_008_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 759 15 15, g32p_row21_traceSegment_008_0759_0015, g32p_row21_traceSegment_008_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_008 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 729 30 30, g32p_row21_traceSegment_008_0729_0030, g32p_row21_traceSegment_008_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 804 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 789 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 789 15 15, g32p_row21_traceSegment_008_0789_0015, g32p_row21_traceSegment_008_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 834 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 819 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 819 15 16, g32p_row21_traceSegment_008_0819_0015, g32p_row21_traceSegment_008_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 789 61 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 789 30 31, g32p_row21_traceSegment_008_0789_0030, g32p_row21_traceSegment_008_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_008 729 121 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 729 60 61, g32p_row21_traceSegment_008_0729_0060, g32p_row21_traceSegment_008_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 850 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 865 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 850 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 850 15 15, g32p_row21_traceSegment_008_0850_0015, g32p_row21_traceSegment_008_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 880 15 16, g32p_row21_traceSegment_008_0880_0015, g32p_row21_traceSegment_008_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 850 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 850 30 31, g32p_row21_traceSegment_008_0850_0030, g32p_row21_traceSegment_008_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_008 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 911 15 15, g32p_row21_traceSegment_008_0911_0015, g32p_row21_traceSegment_008_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_008 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_008 956 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_008_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_008 941 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 941 15 16, g32p_row21_traceSegment_008_0941_0015, g32p_row21_traceSegment_008_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_008 911 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 911 30 31, g32p_row21_traceSegment_008_0911_0030, g32p_row21_traceSegment_008_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_008 850 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 850 61 61, g32p_row21_traceSegment_008_0850_0061, g32p_row21_traceSegment_008_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_008 729 243 = [0, 6, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 729 121 122, g32p_row21_traceSegment_008_0729_0121, g32p_row21_traceSegment_008_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_008 486 486 = [0, 6, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 486 243 243, g32p_row21_traceSegment_008_0486_0243, g32p_row21_traceSegment_008_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_008_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_008 0 972 = [0, 9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_008 0 486 486, g32p_row21_traceSegment_008_0000_0486, g32p_row21_traceSegment_008_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 8 = [0, 9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_008_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_009 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 9 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_009_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 0 15 15, g32p_row21_traceSegment_009_0000_0015, g32p_row21_traceSegment_009_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 30 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 45 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 30 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 30 15 15, g32p_row21_traceSegment_009_0030_0015, g32p_row21_traceSegment_009_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_009 0 60 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 0 30 30, g32p_row21_traceSegment_009_0000_0030, g32p_row21_traceSegment_009_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 60 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 60 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 60 15 15, g32p_row21_traceSegment_009_0060_0015, g32p_row21_traceSegment_009_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 90 15 16, g32p_row21_traceSegment_009_0090_0015, g32p_row21_traceSegment_009_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 60 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 60 30 31, g32p_row21_traceSegment_009_0060_0030, g32p_row21_traceSegment_009_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_009 0 121 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 0 60 61, g32p_row21_traceSegment_009_0000_0060, g32p_row21_traceSegment_009_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 121 15 15, g32p_row21_traceSegment_009_0121_0015, g32p_row21_traceSegment_009_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 151 15 16, g32p_row21_traceSegment_009_0151_0015, g32p_row21_traceSegment_009_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 121 30 31, g32p_row21_traceSegment_009_0121_0030, g32p_row21_traceSegment_009_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 182 15 15, g32p_row21_traceSegment_009_0182_0015, g32p_row21_traceSegment_009_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 227 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 212 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 212 15 16, g32p_row21_traceSegment_009_0212_0015, g32p_row21_traceSegment_009_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 182 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 182 30 31, g32p_row21_traceSegment_009_0182_0030, g32p_row21_traceSegment_009_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_009 121 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 121 61 61, g32p_row21_traceSegment_009_0121_0061, g32p_row21_traceSegment_009_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_009 0 243 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 0 121 122, g32p_row21_traceSegment_009_0000_0121, g32p_row21_traceSegment_009_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 243 15 15, g32p_row21_traceSegment_009_0243_0015, g32p_row21_traceSegment_009_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 273 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 288 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 273 30 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 273 15 15, g32p_row21_traceSegment_009_0273_0015, g32p_row21_traceSegment_009_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_009 243 60 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 243 30 30, g32p_row21_traceSegment_009_0243_0030, g32p_row21_traceSegment_009_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 318 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 303 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 303 15 15, g32p_row21_traceSegment_009_0303_0015, g32p_row21_traceSegment_009_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 333 15 16, g32p_row21_traceSegment_009_0333_0015, g32p_row21_traceSegment_009_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 303 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 303 30 31, g32p_row21_traceSegment_009_0303_0030, g32p_row21_traceSegment_009_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_009 243 121 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 243 60 61, g32p_row21_traceSegment_009_0243_0060, g32p_row21_traceSegment_009_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 364 15 15, g32p_row21_traceSegment_009_0364_0015, g32p_row21_traceSegment_009_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 394 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 409 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 394 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 394 15 16, g32p_row21_traceSegment_009_0394_0015, g32p_row21_traceSegment_009_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 364 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 364 30 31, g32p_row21_traceSegment_009_0364_0030, g32p_row21_traceSegment_009_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 425 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 425 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 425 15 15, g32p_row21_traceSegment_009_0425_0015, g32p_row21_traceSegment_009_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 455 15 16, g32p_row21_traceSegment_009_0455_0015, g32p_row21_traceSegment_009_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 425 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 425 30 31, g32p_row21_traceSegment_009_0425_0030, g32p_row21_traceSegment_009_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_009 364 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 364 61 61, g32p_row21_traceSegment_009_0364_0061, g32p_row21_traceSegment_009_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_009 243 243 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 243 121 122, g32p_row21_traceSegment_009_0243_0121, g32p_row21_traceSegment_009_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_009 0 486 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 0 243 243, g32p_row21_traceSegment_009_0000_0243, g32p_row21_traceSegment_009_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 486 15 15, g32p_row21_traceSegment_009_0486_0015, g32p_row21_traceSegment_009_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 516 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 516 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 516 15 15, g32p_row21_traceSegment_009_0516_0015, g32p_row21_traceSegment_009_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_009 486 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 486 30 30, g32p_row21_traceSegment_009_0486_0030, g32p_row21_traceSegment_009_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 561 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 546 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 546 15 15, g32p_row21_traceSegment_009_0546_0015, g32p_row21_traceSegment_009_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 576 15 16, g32p_row21_traceSegment_009_0576_0015, g32p_row21_traceSegment_009_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 546 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 546 30 31, g32p_row21_traceSegment_009_0546_0030, g32p_row21_traceSegment_009_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_009 486 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 486 60 61, g32p_row21_traceSegment_009_0486_0060, g32p_row21_traceSegment_009_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 622 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 607 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 607 15 15, g32p_row21_traceSegment_009_0607_0015, g32p_row21_traceSegment_009_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 637 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 637 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 637 15 16, g32p_row21_traceSegment_009_0637_0015, g32p_row21_traceSegment_009_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 607 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 607 30 31, g32p_row21_traceSegment_009_0607_0030, g32p_row21_traceSegment_009_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 668 15 15, g32p_row21_traceSegment_009_0668_0015, g32p_row21_traceSegment_009_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 698 15 16, g32p_row21_traceSegment_009_0698_0015, g32p_row21_traceSegment_009_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 668 30 31, g32p_row21_traceSegment_009_0668_0030, g32p_row21_traceSegment_009_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_009 607 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 607 61 61, g32p_row21_traceSegment_009_0607_0061, g32p_row21_traceSegment_009_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_009 486 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 486 121 122, g32p_row21_traceSegment_009_0486_0121, g32p_row21_traceSegment_009_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 729 15 15, g32p_row21_traceSegment_009_0729_0015, g32p_row21_traceSegment_009_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 759 15 15, g32p_row21_traceSegment_009_0759_0015, g32p_row21_traceSegment_009_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_009 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 729 30 30, g32p_row21_traceSegment_009_0729_0030, g32p_row21_traceSegment_009_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 789 15 15, g32p_row21_traceSegment_009_0789_0015, g32p_row21_traceSegment_009_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 819 15 16, g32p_row21_traceSegment_009_0819_0015, g32p_row21_traceSegment_009_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 789 30 31, g32p_row21_traceSegment_009_0789_0030, g32p_row21_traceSegment_009_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_009 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 729 60 61, g32p_row21_traceSegment_009_0729_0060, g32p_row21_traceSegment_009_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 850 15 15, g32p_row21_traceSegment_009_0850_0015, g32p_row21_traceSegment_009_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 880 15 16, g32p_row21_traceSegment_009_0880_0015, g32p_row21_traceSegment_009_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 850 30 31, g32p_row21_traceSegment_009_0850_0030, g32p_row21_traceSegment_009_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_009 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 911 15 15, g32p_row21_traceSegment_009_0911_0015, g32p_row21_traceSegment_009_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_009 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_009 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_009_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_009 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 941 15 16, g32p_row21_traceSegment_009_0941_0015, g32p_row21_traceSegment_009_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_009 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 911 30 31, g32p_row21_traceSegment_009_0911_0030, g32p_row21_traceSegment_009_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_009 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 850 61 61, g32p_row21_traceSegment_009_0850_0061, g32p_row21_traceSegment_009_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_009 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 729 121 122, g32p_row21_traceSegment_009_0729_0121, g32p_row21_traceSegment_009_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_009 486 486 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 486 243 243, g32p_row21_traceSegment_009_0486_0243, g32p_row21_traceSegment_009_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_009_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_009 0 972 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_009 0 486 486, g32p_row21_traceSegment_009_0000_0486, g32p_row21_traceSegment_009_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_009 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 9 = [0, 0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_009_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row21_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 0) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 0) (g32p_literalTraceValue 20 0)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_000]
  decide +kernel

theorem g32p_row21_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 1) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 1) (g32p_literalTraceValue 20 1)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row21_traceCoefficients_001]
  decide +kernel

theorem g32p_row21_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 2) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 2) (g32p_literalTraceValue 20 2)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_002]
  decide +kernel

theorem g32p_row21_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 3) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 3) (g32p_literalTraceValue 20 3)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_003]
  decide +kernel

theorem g32p_row21_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 4) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 4) (g32p_literalTraceValue 20 4)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_004]
  decide +kernel

theorem g32p_row21_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 6) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 6) (g32p_literalTraceValue 20 6)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_006]
  decide +kernel

theorem g32p_row21_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 8) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 8) (g32p_literalTraceValue 20 8)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_008]
  decide +kernel

theorem g32p_row21_tracePolynomial_009 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 9) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 9) (g32p_literalTraceValue 20 9)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_009]
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

private def g32p_row21_traceSegment_010 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 10 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_010_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 0 15 15, g32p_row21_traceSegment_010_0000_0015, g32p_row21_traceSegment_010_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 30 15 15, g32p_row21_traceSegment_010_0030_0015, g32p_row21_traceSegment_010_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_010 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 0 30 30, g32p_row21_traceSegment_010_0000_0030, g32p_row21_traceSegment_010_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 60 15 15, g32p_row21_traceSegment_010_0060_0015, g32p_row21_traceSegment_010_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 90 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 105 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 90 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 90 15 16, g32p_row21_traceSegment_010_0090_0015, g32p_row21_traceSegment_010_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 60 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 60 30 31, g32p_row21_traceSegment_010_0060_0030, g32p_row21_traceSegment_010_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_010 0 121 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 0 60 61, g32p_row21_traceSegment_010_0000_0060, g32p_row21_traceSegment_010_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 121 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 121 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 121 15 15, g32p_row21_traceSegment_010_0121_0015, g32p_row21_traceSegment_010_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 151 15 16, g32p_row21_traceSegment_010_0151_0015, g32p_row21_traceSegment_010_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 121 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 121 30 31, g32p_row21_traceSegment_010_0121_0030, g32p_row21_traceSegment_010_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 182 15 15, g32p_row21_traceSegment_010_0182_0015, g32p_row21_traceSegment_010_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 212 15 16, g32p_row21_traceSegment_010_0212_0015, g32p_row21_traceSegment_010_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 182 30 31, g32p_row21_traceSegment_010_0182_0030, g32p_row21_traceSegment_010_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_010 121 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 121 61 61, g32p_row21_traceSegment_010_0121_0061, g32p_row21_traceSegment_010_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_010 0 243 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 0 121 122, g32p_row21_traceSegment_010_0000_0121, g32p_row21_traceSegment_010_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 243 15 15, g32p_row21_traceSegment_010_0243_0015, g32p_row21_traceSegment_010_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 273 15 15, g32p_row21_traceSegment_010_0273_0015, g32p_row21_traceSegment_010_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_010 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 243 30 30, g32p_row21_traceSegment_010_0243_0030, g32p_row21_traceSegment_010_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 303 15 15, g32p_row21_traceSegment_010_0303_0015, g32p_row21_traceSegment_010_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 333 15 = [3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 348 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 333 31 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 333 15 16, g32p_row21_traceSegment_010_0333_0015, g32p_row21_traceSegment_010_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 303 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 303 30 31, g32p_row21_traceSegment_010_0303_0030, g32p_row21_traceSegment_010_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_010 243 121 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 243 60 61, g32p_row21_traceSegment_010_0243_0060, g32p_row21_traceSegment_010_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 364 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 364 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 364 15 15, g32p_row21_traceSegment_010_0364_0015, g32p_row21_traceSegment_010_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 394 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 394 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 394 15 16, g32p_row21_traceSegment_010_0394_0015, g32p_row21_traceSegment_010_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 364 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 364 30 31, g32p_row21_traceSegment_010_0364_0030, g32p_row21_traceSegment_010_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 425 15 15, g32p_row21_traceSegment_010_0425_0015, g32p_row21_traceSegment_010_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 455 15 16, g32p_row21_traceSegment_010_0455_0015, g32p_row21_traceSegment_010_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 425 30 31, g32p_row21_traceSegment_010_0425_0030, g32p_row21_traceSegment_010_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_010 364 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 364 61 61, g32p_row21_traceSegment_010_0364_0061, g32p_row21_traceSegment_010_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_010 243 243 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 243 121 122, g32p_row21_traceSegment_010_0243_0121, g32p_row21_traceSegment_010_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_010 0 486 = [6, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 0 243 243, g32p_row21_traceSegment_010_0000_0243, g32p_row21_traceSegment_010_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 501 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 486 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 486 15 15, g32p_row21_traceSegment_010_0486_0015, g32p_row21_traceSegment_010_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 516 15 15, g32p_row21_traceSegment_010_0516_0015, g32p_row21_traceSegment_010_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_010 486 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 486 30 30, g32p_row21_traceSegment_010_0486_0030, g32p_row21_traceSegment_010_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 546 15 15, g32p_row21_traceSegment_010_0546_0015, g32p_row21_traceSegment_010_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 576 15 16, g32p_row21_traceSegment_010_0576_0015, g32p_row21_traceSegment_010_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 546 30 31, g32p_row21_traceSegment_010_0546_0030, g32p_row21_traceSegment_010_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_010 486 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 486 60 61, g32p_row21_traceSegment_010_0486_0060, g32p_row21_traceSegment_010_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 607 15 15, g32p_row21_traceSegment_010_0607_0015, g32p_row21_traceSegment_010_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 637 15 16, g32p_row21_traceSegment_010_0637_0015, g32p_row21_traceSegment_010_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 607 30 31, g32p_row21_traceSegment_010_0607_0030, g32p_row21_traceSegment_010_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 683 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 668 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 668 15 15, g32p_row21_traceSegment_010_0668_0015, g32p_row21_traceSegment_010_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 698 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 713 16 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 698 31 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 698 15 16, g32p_row21_traceSegment_010_0698_0015, g32p_row21_traceSegment_010_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 668 61 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 668 30 31, g32p_row21_traceSegment_010_0668_0030, g32p_row21_traceSegment_010_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_010 607 122 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 607 61 61, g32p_row21_traceSegment_010_0607_0061, g32p_row21_traceSegment_010_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_010 486 243 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 486 121 122, g32p_row21_traceSegment_010_0486_0121, g32p_row21_traceSegment_010_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 729 15 15, g32p_row21_traceSegment_010_0729_0015, g32p_row21_traceSegment_010_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 759 15 15, g32p_row21_traceSegment_010_0759_0015, g32p_row21_traceSegment_010_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_010 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 729 30 30, g32p_row21_traceSegment_010_0729_0030, g32p_row21_traceSegment_010_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 789 15 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 789 30 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 789 15 15, g32p_row21_traceSegment_010_0789_0015, g32p_row21_traceSegment_010_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 819 15 16, g32p_row21_traceSegment_010_0819_0015, g32p_row21_traceSegment_010_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 789 61 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 789 30 31, g32p_row21_traceSegment_010_0789_0030, g32p_row21_traceSegment_010_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_010 729 121 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 729 60 61, g32p_row21_traceSegment_010_0729_0060, g32p_row21_traceSegment_010_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 850 15 15, g32p_row21_traceSegment_010_0850_0015, g32p_row21_traceSegment_010_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 880 15 16, g32p_row21_traceSegment_010_0880_0015, g32p_row21_traceSegment_010_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 850 30 31, g32p_row21_traceSegment_010_0850_0030, g32p_row21_traceSegment_010_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_010 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 911 15 15, g32p_row21_traceSegment_010_0911_0015, g32p_row21_traceSegment_010_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_010 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_010 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_010_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_010 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 941 15 16, g32p_row21_traceSegment_010_0941_0015, g32p_row21_traceSegment_010_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_010 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 911 30 31, g32p_row21_traceSegment_010_0911_0030, g32p_row21_traceSegment_010_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_010 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 850 61 61, g32p_row21_traceSegment_010_0850_0061, g32p_row21_traceSegment_010_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_010 729 243 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 729 121 122, g32p_row21_traceSegment_010_0729_0121, g32p_row21_traceSegment_010_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_010 486 486 = [3, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 486 243 243, g32p_row21_traceSegment_010_0486_0243, g32p_row21_traceSegment_010_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_010_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_010 0 972 = [9, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_010 0 486 486, g32p_row21_traceSegment_010_0000_0486, g32p_row21_traceSegment_010_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 10 = [9, 0, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_010_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_011 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 11 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_011_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 0 15 15, g32p_row21_traceSegment_011_0000_0015, g32p_row21_traceSegment_011_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 30 15 15, g32p_row21_traceSegment_011_0030_0015, g32p_row21_traceSegment_011_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_011 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 0 30 30, g32p_row21_traceSegment_011_0000_0030, g32p_row21_traceSegment_011_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 60 15 15, g32p_row21_traceSegment_011_0060_0015, g32p_row21_traceSegment_011_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 90 15 16, g32p_row21_traceSegment_011_0090_0015, g32p_row21_traceSegment_011_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 60 30 31, g32p_row21_traceSegment_011_0060_0030, g32p_row21_traceSegment_011_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_011 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 0 60 61, g32p_row21_traceSegment_011_0000_0060, g32p_row21_traceSegment_011_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 121 15 15, g32p_row21_traceSegment_011_0121_0015, g32p_row21_traceSegment_011_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 151 15 16, g32p_row21_traceSegment_011_0151_0015, g32p_row21_traceSegment_011_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 121 30 31, g32p_row21_traceSegment_011_0121_0030, g32p_row21_traceSegment_011_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 182 15 15, g32p_row21_traceSegment_011_0182_0015, g32p_row21_traceSegment_011_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 212 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 227 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 212 31 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 212 15 16, g32p_row21_traceSegment_011_0212_0015, g32p_row21_traceSegment_011_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 182 61 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 182 30 31, g32p_row21_traceSegment_011_0182_0030, g32p_row21_traceSegment_011_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_011 121 122 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 121 61 61, g32p_row21_traceSegment_011_0121_0061, g32p_row21_traceSegment_011_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_011 0 243 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 0 121 122, g32p_row21_traceSegment_011_0000_0121, g32p_row21_traceSegment_011_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 243 15 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 243 30 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 243 15 15, g32p_row21_traceSegment_011_0243_0015, g32p_row21_traceSegment_011_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 273 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 273 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 273 15 15, g32p_row21_traceSegment_011_0273_0015, g32p_row21_traceSegment_011_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_011 243 60 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 243 30 30, g32p_row21_traceSegment_011_0243_0030, g32p_row21_traceSegment_011_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 303 15 15, g32p_row21_traceSegment_011_0303_0015, g32p_row21_traceSegment_011_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 333 15 16, g32p_row21_traceSegment_011_0333_0015, g32p_row21_traceSegment_011_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 303 30 31, g32p_row21_traceSegment_011_0303_0030, g32p_row21_traceSegment_011_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_011 243 121 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 243 60 61, g32p_row21_traceSegment_011_0243_0060, g32p_row21_traceSegment_011_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 364 15 15, g32p_row21_traceSegment_011_0364_0015, g32p_row21_traceSegment_011_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 394 15 16, g32p_row21_traceSegment_011_0394_0015, g32p_row21_traceSegment_011_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 364 30 31, g32p_row21_traceSegment_011_0364_0030, g32p_row21_traceSegment_011_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 425 15 15, g32p_row21_traceSegment_011_0425_0015, g32p_row21_traceSegment_011_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 455 15 16, g32p_row21_traceSegment_011_0455_0015, g32p_row21_traceSegment_011_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 425 30 31, g32p_row21_traceSegment_011_0425_0030, g32p_row21_traceSegment_011_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_011 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 364 61 61, g32p_row21_traceSegment_011_0364_0061, g32p_row21_traceSegment_011_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_011 243 243 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 243 121 122, g32p_row21_traceSegment_011_0243_0121, g32p_row21_traceSegment_011_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_011 0 486 = [3, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 0 243 243, g32p_row21_traceSegment_011_0000_0243, g32p_row21_traceSegment_011_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 486 15 15, g32p_row21_traceSegment_011_0486_0015, g32p_row21_traceSegment_011_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 516 15 15, g32p_row21_traceSegment_011_0516_0015, g32p_row21_traceSegment_011_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_011 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 486 30 30, g32p_row21_traceSegment_011_0486_0030, g32p_row21_traceSegment_011_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 546 15 15, g32p_row21_traceSegment_011_0546_0015, g32p_row21_traceSegment_011_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 576 15 16, g32p_row21_traceSegment_011_0576_0015, g32p_row21_traceSegment_011_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 546 30 31, g32p_row21_traceSegment_011_0546_0030, g32p_row21_traceSegment_011_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_011 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 486 60 61, g32p_row21_traceSegment_011_0486_0060, g32p_row21_traceSegment_011_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 607 15 15, g32p_row21_traceSegment_011_0607_0015, g32p_row21_traceSegment_011_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 637 15 16, g32p_row21_traceSegment_011_0637_0015, g32p_row21_traceSegment_011_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 607 30 31, g32p_row21_traceSegment_011_0607_0030, g32p_row21_traceSegment_011_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 668 15 15, g32p_row21_traceSegment_011_0668_0015, g32p_row21_traceSegment_011_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 698 15 16, g32p_row21_traceSegment_011_0698_0015, g32p_row21_traceSegment_011_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 668 30 31, g32p_row21_traceSegment_011_0668_0030, g32p_row21_traceSegment_011_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_011 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 607 61 61, g32p_row21_traceSegment_011_0607_0061, g32p_row21_traceSegment_011_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_011 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 486 121 122, g32p_row21_traceSegment_011_0486_0121, g32p_row21_traceSegment_011_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 729 15 15, g32p_row21_traceSegment_011_0729_0015, g32p_row21_traceSegment_011_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 759 15 15, g32p_row21_traceSegment_011_0759_0015, g32p_row21_traceSegment_011_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_011 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 729 30 30, g32p_row21_traceSegment_011_0729_0030, g32p_row21_traceSegment_011_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 789 15 15, g32p_row21_traceSegment_011_0789_0015, g32p_row21_traceSegment_011_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 819 15 16, g32p_row21_traceSegment_011_0819_0015, g32p_row21_traceSegment_011_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 789 30 31, g32p_row21_traceSegment_011_0789_0030, g32p_row21_traceSegment_011_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_011 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 729 60 61, g32p_row21_traceSegment_011_0729_0060, g32p_row21_traceSegment_011_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 850 15 15, g32p_row21_traceSegment_011_0850_0015, g32p_row21_traceSegment_011_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 880 15 16, g32p_row21_traceSegment_011_0880_0015, g32p_row21_traceSegment_011_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 850 30 31, g32p_row21_traceSegment_011_0850_0030, g32p_row21_traceSegment_011_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_011 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 911 15 15, g32p_row21_traceSegment_011_0911_0015, g32p_row21_traceSegment_011_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_011 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_011 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_011_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_011 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 941 15 16, g32p_row21_traceSegment_011_0941_0015, g32p_row21_traceSegment_011_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_011 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 911 30 31, g32p_row21_traceSegment_011_0911_0030, g32p_row21_traceSegment_011_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_011 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 850 61 61, g32p_row21_traceSegment_011_0850_0061, g32p_row21_traceSegment_011_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_011 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 729 121 122, g32p_row21_traceSegment_011_0729_0121, g32p_row21_traceSegment_011_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_011 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 486 243 243, g32p_row21_traceSegment_011_0486_0243, g32p_row21_traceSegment_011_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_011_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_011 0 972 = [3, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_011 0 486 486, g32p_row21_traceSegment_011_0000_0486, g32p_row21_traceSegment_011_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 11 = [3, 0, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_011_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_012 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 12 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_012_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 0 15 15, g32p_row21_traceSegment_012_0000_0015, g32p_row21_traceSegment_012_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 30 15 15, g32p_row21_traceSegment_012_0030_0015, g32p_row21_traceSegment_012_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_012 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 0 30 30, g32p_row21_traceSegment_012_0000_0030, g32p_row21_traceSegment_012_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 60 15 15, g32p_row21_traceSegment_012_0060_0015, g32p_row21_traceSegment_012_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 90 15 16, g32p_row21_traceSegment_012_0090_0015, g32p_row21_traceSegment_012_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 60 30 31, g32p_row21_traceSegment_012_0060_0030, g32p_row21_traceSegment_012_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_012 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 0 60 61, g32p_row21_traceSegment_012_0000_0060, g32p_row21_traceSegment_012_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 121 15 15, g32p_row21_traceSegment_012_0121_0015, g32p_row21_traceSegment_012_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 151 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 166 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 151 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 151 15 16, g32p_row21_traceSegment_012_0151_0015, g32p_row21_traceSegment_012_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 121 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 121 30 31, g32p_row21_traceSegment_012_0121_0030, g32p_row21_traceSegment_012_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 182 15 15, g32p_row21_traceSegment_012_0182_0015, g32p_row21_traceSegment_012_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 212 15 16, g32p_row21_traceSegment_012_0212_0015, g32p_row21_traceSegment_012_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 182 30 31, g32p_row21_traceSegment_012_0182_0030, g32p_row21_traceSegment_012_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_012 121 122 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 121 61 61, g32p_row21_traceSegment_012_0121_0061, g32p_row21_traceSegment_012_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_012 0 243 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 0 121 122, g32p_row21_traceSegment_012_0000_0121, g32p_row21_traceSegment_012_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 243 15 15, g32p_row21_traceSegment_012_0243_0015, g32p_row21_traceSegment_012_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 273 15 15, g32p_row21_traceSegment_012_0273_0015, g32p_row21_traceSegment_012_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_012 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 243 30 30, g32p_row21_traceSegment_012_0243_0030, g32p_row21_traceSegment_012_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 303 15 15, g32p_row21_traceSegment_012_0303_0015, g32p_row21_traceSegment_012_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 333 15 16, g32p_row21_traceSegment_012_0333_0015, g32p_row21_traceSegment_012_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 303 30 31, g32p_row21_traceSegment_012_0303_0030, g32p_row21_traceSegment_012_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_012 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 243 60 61, g32p_row21_traceSegment_012_0243_0060, g32p_row21_traceSegment_012_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 364 15 15, g32p_row21_traceSegment_012_0364_0015, g32p_row21_traceSegment_012_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 394 15 16, g32p_row21_traceSegment_012_0394_0015, g32p_row21_traceSegment_012_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 364 30 31, g32p_row21_traceSegment_012_0364_0030, g32p_row21_traceSegment_012_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 425 15 15, g32p_row21_traceSegment_012_0425_0015, g32p_row21_traceSegment_012_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 455 15 16, g32p_row21_traceSegment_012_0455_0015, g32p_row21_traceSegment_012_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 425 30 31, g32p_row21_traceSegment_012_0425_0030, g32p_row21_traceSegment_012_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_012 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 364 61 61, g32p_row21_traceSegment_012_0364_0061, g32p_row21_traceSegment_012_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_012 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 243 121 122, g32p_row21_traceSegment_012_0243_0121, g32p_row21_traceSegment_012_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_012 0 486 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 0 243 243, g32p_row21_traceSegment_012_0000_0243, g32p_row21_traceSegment_012_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 486 15 15, g32p_row21_traceSegment_012_0486_0015, g32p_row21_traceSegment_012_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 516 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 531 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 516 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 516 15 15, g32p_row21_traceSegment_012_0516_0015, g32p_row21_traceSegment_012_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_012 486 60 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 486 30 30, g32p_row21_traceSegment_012_0486_0030, g32p_row21_traceSegment_012_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 546 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 561 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 546 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 546 15 15, g32p_row21_traceSegment_012_0546_0015, g32p_row21_traceSegment_012_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 591 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 576 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 576 15 16, g32p_row21_traceSegment_012_0576_0015, g32p_row21_traceSegment_012_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 546 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 546 30 31, g32p_row21_traceSegment_012_0546_0030, g32p_row21_traceSegment_012_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_012 486 121 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 486 60 61, g32p_row21_traceSegment_012_0486_0060, g32p_row21_traceSegment_012_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 607 15 15, g32p_row21_traceSegment_012_0607_0015, g32p_row21_traceSegment_012_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 652 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 637 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 637 15 16, g32p_row21_traceSegment_012_0637_0015, g32p_row21_traceSegment_012_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 607 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 607 30 31, g32p_row21_traceSegment_012_0607_0030, g32p_row21_traceSegment_012_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 668 15 15, g32p_row21_traceSegment_012_0668_0015, g32p_row21_traceSegment_012_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 698 15 16, g32p_row21_traceSegment_012_0698_0015, g32p_row21_traceSegment_012_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 668 30 31, g32p_row21_traceSegment_012_0668_0030, g32p_row21_traceSegment_012_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_012 607 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 607 61 61, g32p_row21_traceSegment_012_0607_0061, g32p_row21_traceSegment_012_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_012 486 243 = [8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 486 121 122, g32p_row21_traceSegment_012_0486_0121, g32p_row21_traceSegment_012_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 729 15 15, g32p_row21_traceSegment_012_0729_0015, g32p_row21_traceSegment_012_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 759 15 15, g32p_row21_traceSegment_012_0759_0015, g32p_row21_traceSegment_012_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_012 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 729 30 30, g32p_row21_traceSegment_012_0729_0030, g32p_row21_traceSegment_012_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 789 15 15, g32p_row21_traceSegment_012_0789_0015, g32p_row21_traceSegment_012_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 819 15 16, g32p_row21_traceSegment_012_0819_0015, g32p_row21_traceSegment_012_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 789 30 31, g32p_row21_traceSegment_012_0789_0030, g32p_row21_traceSegment_012_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_012 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 729 60 61, g32p_row21_traceSegment_012_0729_0060, g32p_row21_traceSegment_012_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 850 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 865 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 850 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 850 15 15, g32p_row21_traceSegment_012_0850_0015, g32p_row21_traceSegment_012_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 880 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 895 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 880 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 880 15 16, g32p_row21_traceSegment_012_0880_0015, g32p_row21_traceSegment_012_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 850 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 850 30 31, g32p_row21_traceSegment_012_0850_0030, g32p_row21_traceSegment_012_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 911 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 926 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_012 911 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 911 15 15, g32p_row21_traceSegment_012_0911_0015, g32p_row21_traceSegment_012_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_012 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_012 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_012_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_012 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 941 15 16, g32p_row21_traceSegment_012_0941_0015, g32p_row21_traceSegment_012_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_012 911 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 911 30 31, g32p_row21_traceSegment_012_0911_0030, g32p_row21_traceSegment_012_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_012 850 122 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 850 61 61, g32p_row21_traceSegment_012_0850_0061, g32p_row21_traceSegment_012_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_012 729 243 = [7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 729 121 122, g32p_row21_traceSegment_012_0729_0121, g32p_row21_traceSegment_012_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_012 486 486 = [15] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 486 243 243, g32p_row21_traceSegment_012_0486_0243, g32p_row21_traceSegment_012_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_012_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_012 0 972 = [18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_012 0 486 486, g32p_row21_traceSegment_012_0000_0486, g32p_row21_traceSegment_012_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_012 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 12 = [18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_012_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_014 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 14 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_014_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 0 15 15, g32p_row21_traceSegment_014_0000_0015, g32p_row21_traceSegment_014_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 30 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 30 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 30 15 15, g32p_row21_traceSegment_014_0030_0015, g32p_row21_traceSegment_014_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_014 0 60 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 0 30 30, g32p_row21_traceSegment_014_0000_0030, g32p_row21_traceSegment_014_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 60 15 15, g32p_row21_traceSegment_014_0060_0015, g32p_row21_traceSegment_014_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 90 15 16, g32p_row21_traceSegment_014_0090_0015, g32p_row21_traceSegment_014_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 60 30 31, g32p_row21_traceSegment_014_0060_0030, g32p_row21_traceSegment_014_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_014 0 121 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 0 60 61, g32p_row21_traceSegment_014_0000_0060, g32p_row21_traceSegment_014_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 121 15 15, g32p_row21_traceSegment_014_0121_0015, g32p_row21_traceSegment_014_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 151 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 166 16 = [0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 151 31 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 151 15 16, g32p_row21_traceSegment_014_0151_0015, g32p_row21_traceSegment_014_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 121 61 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 121 30 31, g32p_row21_traceSegment_014_0121_0030, g32p_row21_traceSegment_014_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 182 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 182 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 182 15 15, g32p_row21_traceSegment_014_0182_0015, g32p_row21_traceSegment_014_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 212 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 212 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 212 15 16, g32p_row21_traceSegment_014_0212_0015, g32p_row21_traceSegment_014_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 182 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 182 30 31, g32p_row21_traceSegment_014_0182_0030, g32p_row21_traceSegment_014_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_014 121 122 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 121 61 61, g32p_row21_traceSegment_014_0121_0061, g32p_row21_traceSegment_014_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_014 0 243 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 0 121 122, g32p_row21_traceSegment_014_0000_0121, g32p_row21_traceSegment_014_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 258 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 243 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 243 15 15, g32p_row21_traceSegment_014_0243_0015, g32p_row21_traceSegment_014_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 273 15 15, g32p_row21_traceSegment_014_0273_0015, g32p_row21_traceSegment_014_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_014 243 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 243 30 30, g32p_row21_traceSegment_014_0243_0030, g32p_row21_traceSegment_014_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 303 15 15, g32p_row21_traceSegment_014_0303_0015, g32p_row21_traceSegment_014_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 333 15 16, g32p_row21_traceSegment_014_0333_0015, g32p_row21_traceSegment_014_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 303 30 31, g32p_row21_traceSegment_014_0303_0030, g32p_row21_traceSegment_014_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_014 243 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 243 60 61, g32p_row21_traceSegment_014_0243_0060, g32p_row21_traceSegment_014_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 364 15 15, g32p_row21_traceSegment_014_0364_0015, g32p_row21_traceSegment_014_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 394 15 16, g32p_row21_traceSegment_014_0394_0015, g32p_row21_traceSegment_014_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 364 30 31, g32p_row21_traceSegment_014_0364_0030, g32p_row21_traceSegment_014_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 440 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 425 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 425 15 15, g32p_row21_traceSegment_014_0425_0015, g32p_row21_traceSegment_014_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 470 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 455 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 455 15 16, g32p_row21_traceSegment_014_0455_0015, g32p_row21_traceSegment_014_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 425 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 425 30 31, g32p_row21_traceSegment_014_0425_0030, g32p_row21_traceSegment_014_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_014 364 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 364 61 61, g32p_row21_traceSegment_014_0364_0061, g32p_row21_traceSegment_014_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_014 243 243 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 243 121 122, g32p_row21_traceSegment_014_0243_0121, g32p_row21_traceSegment_014_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_014 0 486 = [0, 13] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 0 243 243, g32p_row21_traceSegment_014_0000_0243, g32p_row21_traceSegment_014_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 486 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 486 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 486 15 15, g32p_row21_traceSegment_014_0486_0015, g32p_row21_traceSegment_014_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 516 15 15, g32p_row21_traceSegment_014_0516_0015, g32p_row21_traceSegment_014_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_014 486 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 486 30 30, g32p_row21_traceSegment_014_0486_0030, g32p_row21_traceSegment_014_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 546 15 15, g32p_row21_traceSegment_014_0546_0015, g32p_row21_traceSegment_014_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 576 15 16, g32p_row21_traceSegment_014_0576_0015, g32p_row21_traceSegment_014_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 546 30 31, g32p_row21_traceSegment_014_0546_0030, g32p_row21_traceSegment_014_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_014 486 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 486 60 61, g32p_row21_traceSegment_014_0486_0060, g32p_row21_traceSegment_014_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 622 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 607 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 607 15 15, g32p_row21_traceSegment_014_0607_0015, g32p_row21_traceSegment_014_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 637 15 16, g32p_row21_traceSegment_014_0637_0015, g32p_row21_traceSegment_014_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 607 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 607 30 31, g32p_row21_traceSegment_014_0607_0030, g32p_row21_traceSegment_014_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 668 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 668 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 668 15 15, g32p_row21_traceSegment_014_0668_0015, g32p_row21_traceSegment_014_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 698 15 16, g32p_row21_traceSegment_014_0698_0015, g32p_row21_traceSegment_014_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 668 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 668 30 31, g32p_row21_traceSegment_014_0668_0030, g32p_row21_traceSegment_014_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_014 607 122 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 607 61 61, g32p_row21_traceSegment_014_0607_0061, g32p_row21_traceSegment_014_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_014 486 243 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 486 121 122, g32p_row21_traceSegment_014_0486_0121, g32p_row21_traceSegment_014_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 729 15 15, g32p_row21_traceSegment_014_0729_0015, g32p_row21_traceSegment_014_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 759 15 15, g32p_row21_traceSegment_014_0759_0015, g32p_row21_traceSegment_014_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_014 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 729 30 30, g32p_row21_traceSegment_014_0729_0030, g32p_row21_traceSegment_014_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 789 15 15, g32p_row21_traceSegment_014_0789_0015, g32p_row21_traceSegment_014_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 834 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 819 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 819 15 16, g32p_row21_traceSegment_014_0819_0015, g32p_row21_traceSegment_014_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 789 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 789 30 31, g32p_row21_traceSegment_014_0789_0030, g32p_row21_traceSegment_014_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_014 729 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 729 60 61, g32p_row21_traceSegment_014_0729_0060, g32p_row21_traceSegment_014_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 850 15 15, g32p_row21_traceSegment_014_0850_0015, g32p_row21_traceSegment_014_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 880 15 16, g32p_row21_traceSegment_014_0880_0015, g32p_row21_traceSegment_014_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 850 30 31, g32p_row21_traceSegment_014_0850_0030, g32p_row21_traceSegment_014_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_014 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 911 15 15, g32p_row21_traceSegment_014_0911_0015, g32p_row21_traceSegment_014_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_014 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_014 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_014_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_014 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 941 15 16, g32p_row21_traceSegment_014_0941_0015, g32p_row21_traceSegment_014_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_014 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 911 30 31, g32p_row21_traceSegment_014_0911_0030, g32p_row21_traceSegment_014_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_014 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 850 61 61, g32p_row21_traceSegment_014_0850_0061, g32p_row21_traceSegment_014_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_014 729 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 729 121 122, g32p_row21_traceSegment_014_0729_0121, g32p_row21_traceSegment_014_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_014 486 486 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 486 243 243, g32p_row21_traceSegment_014_0486_0243, g32p_row21_traceSegment_014_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_014_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_014 0 972 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_014 0 486 486, g32p_row21_traceSegment_014_0000_0486, g32p_row21_traceSegment_014_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_014 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 14 = [0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_014_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_015 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 15 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_015_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 0 15 15, g32p_row21_traceSegment_015_0000_0015, g32p_row21_traceSegment_015_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 30 15 15, g32p_row21_traceSegment_015_0030_0015, g32p_row21_traceSegment_015_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_015 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 0 30 30, g32p_row21_traceSegment_015_0000_0030, g32p_row21_traceSegment_015_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 60 15 15, g32p_row21_traceSegment_015_0060_0015, g32p_row21_traceSegment_015_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 90 15 = [0, 4] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 105 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 90 31 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 90 15 16, g32p_row21_traceSegment_015_0090_0015, g32p_row21_traceSegment_015_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 60 61 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 60 30 31, g32p_row21_traceSegment_015_0060_0030, g32p_row21_traceSegment_015_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_015 0 121 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 0 60 61, g32p_row21_traceSegment_015_0000_0060, g32p_row21_traceSegment_015_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 121 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 121 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 121 15 15, g32p_row21_traceSegment_015_0121_0015, g32p_row21_traceSegment_015_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 151 15 16, g32p_row21_traceSegment_015_0151_0015, g32p_row21_traceSegment_015_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 121 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 121 30 31, g32p_row21_traceSegment_015_0121_0030, g32p_row21_traceSegment_015_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 182 15 15, g32p_row21_traceSegment_015_0182_0015, g32p_row21_traceSegment_015_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 212 15 16, g32p_row21_traceSegment_015_0212_0015, g32p_row21_traceSegment_015_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 182 30 31, g32p_row21_traceSegment_015_0182_0030, g32p_row21_traceSegment_015_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_015 121 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 121 61 61, g32p_row21_traceSegment_015_0121_0061, g32p_row21_traceSegment_015_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_015 0 243 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 0 121 122, g32p_row21_traceSegment_015_0000_0121, g32p_row21_traceSegment_015_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 243 15 15, g32p_row21_traceSegment_015_0243_0015, g32p_row21_traceSegment_015_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 273 15 15, g32p_row21_traceSegment_015_0273_0015, g32p_row21_traceSegment_015_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_015 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 243 30 30, g32p_row21_traceSegment_015_0243_0030, g32p_row21_traceSegment_015_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 303 15 15, g32p_row21_traceSegment_015_0303_0015, g32p_row21_traceSegment_015_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 333 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 333 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 333 15 16, g32p_row21_traceSegment_015_0333_0015, g32p_row21_traceSegment_015_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 303 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 303 30 31, g32p_row21_traceSegment_015_0303_0030, g32p_row21_traceSegment_015_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_015 243 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 243 60 61, g32p_row21_traceSegment_015_0243_0060, g32p_row21_traceSegment_015_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 364 15 15, g32p_row21_traceSegment_015_0364_0015, g32p_row21_traceSegment_015_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 394 15 16, g32p_row21_traceSegment_015_0394_0015, g32p_row21_traceSegment_015_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 364 30 31, g32p_row21_traceSegment_015_0364_0030, g32p_row21_traceSegment_015_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 425 15 15, g32p_row21_traceSegment_015_0425_0015, g32p_row21_traceSegment_015_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 455 15 16, g32p_row21_traceSegment_015_0455_0015, g32p_row21_traceSegment_015_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 425 30 31, g32p_row21_traceSegment_015_0425_0030, g32p_row21_traceSegment_015_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_015 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 364 61 61, g32p_row21_traceSegment_015_0364_0061, g32p_row21_traceSegment_015_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_015 243 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 243 121 122, g32p_row21_traceSegment_015_0243_0121, g32p_row21_traceSegment_015_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_015 0 486 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 0 243 243, g32p_row21_traceSegment_015_0000_0243, g32p_row21_traceSegment_015_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 486 15 15, g32p_row21_traceSegment_015_0486_0015, g32p_row21_traceSegment_015_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 531 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 516 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 516 15 15, g32p_row21_traceSegment_015_0516_0015, g32p_row21_traceSegment_015_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_015 486 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 486 30 30, g32p_row21_traceSegment_015_0486_0030, g32p_row21_traceSegment_015_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 546 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 561 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 546 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 546 15 15, g32p_row21_traceSegment_015_0546_0015, g32p_row21_traceSegment_015_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 576 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 576 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 576 15 16, g32p_row21_traceSegment_015_0576_0015, g32p_row21_traceSegment_015_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 546 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 546 30 31, g32p_row21_traceSegment_015_0546_0030, g32p_row21_traceSegment_015_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_015 486 121 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 486 60 61, g32p_row21_traceSegment_015_0486_0060, g32p_row21_traceSegment_015_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 607 15 15, g32p_row21_traceSegment_015_0607_0015, g32p_row21_traceSegment_015_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 637 15 16, g32p_row21_traceSegment_015_0637_0015, g32p_row21_traceSegment_015_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 607 30 31, g32p_row21_traceSegment_015_0607_0030, g32p_row21_traceSegment_015_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 668 15 15, g32p_row21_traceSegment_015_0668_0015, g32p_row21_traceSegment_015_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 698 15 16, g32p_row21_traceSegment_015_0698_0015, g32p_row21_traceSegment_015_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 668 30 31, g32p_row21_traceSegment_015_0668_0030, g32p_row21_traceSegment_015_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_015 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 607 61 61, g32p_row21_traceSegment_015_0607_0061, g32p_row21_traceSegment_015_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_015 486 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 486 121 122, g32p_row21_traceSegment_015_0486_0121, g32p_row21_traceSegment_015_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 744 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 729 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 729 15 15, g32p_row21_traceSegment_015_0729_0015, g32p_row21_traceSegment_015_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 759 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 759 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 759 15 15, g32p_row21_traceSegment_015_0759_0015, g32p_row21_traceSegment_015_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_015 729 60 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 729 30 30, g32p_row21_traceSegment_015_0729_0030, g32p_row21_traceSegment_015_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 789 15 15, g32p_row21_traceSegment_015_0789_0015, g32p_row21_traceSegment_015_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 819 15 16, g32p_row21_traceSegment_015_0819_0015, g32p_row21_traceSegment_015_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 789 30 31, g32p_row21_traceSegment_015_0789_0030, g32p_row21_traceSegment_015_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_015 729 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 729 60 61, g32p_row21_traceSegment_015_0729_0060, g32p_row21_traceSegment_015_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 865 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 850 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 850 15 15, g32p_row21_traceSegment_015_0850_0015, g32p_row21_traceSegment_015_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 880 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 880 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 880 15 16, g32p_row21_traceSegment_015_0880_0015, g32p_row21_traceSegment_015_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 850 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 850 30 31, g32p_row21_traceSegment_015_0850_0030, g32p_row21_traceSegment_015_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_015 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 911 15 15, g32p_row21_traceSegment_015_0911_0015, g32p_row21_traceSegment_015_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_015 941 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_015 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_015_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_015 941 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 941 15 16, g32p_row21_traceSegment_015_0941_0015, g32p_row21_traceSegment_015_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_015 911 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 911 30 31, g32p_row21_traceSegment_015_0911_0030, g32p_row21_traceSegment_015_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_015 850 122 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 850 61 61, g32p_row21_traceSegment_015_0850_0061, g32p_row21_traceSegment_015_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_015 729 243 = [4, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 729 121 122, g32p_row21_traceSegment_015_0729_0121, g32p_row21_traceSegment_015_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_015 486 486 = [9, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 486 243 243, g32p_row21_traceSegment_015_0486_0243, g32p_row21_traceSegment_015_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_015_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_015 0 972 = [9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_015 0 486 486, g32p_row21_traceSegment_015_0000_0486, g32p_row21_traceSegment_015_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 15 = [9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_015_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_018 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 18 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_018_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 0 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 15 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 0 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 0 15 15, g32p_row21_traceSegment_018_0000_0015, g32p_row21_traceSegment_018_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 30 15 15, g32p_row21_traceSegment_018_0030_0015, g32p_row21_traceSegment_018_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_018 0 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 0 30 30, g32p_row21_traceSegment_018_0000_0030, g32p_row21_traceSegment_018_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 60 15 15, g32p_row21_traceSegment_018_0060_0015, g32p_row21_traceSegment_018_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 90 15 16, g32p_row21_traceSegment_018_0090_0015, g32p_row21_traceSegment_018_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 60 30 31, g32p_row21_traceSegment_018_0060_0030, g32p_row21_traceSegment_018_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_018 0 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 0 60 61, g32p_row21_traceSegment_018_0000_0060, g32p_row21_traceSegment_018_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 121 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 121 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 121 15 15, g32p_row21_traceSegment_018_0121_0015, g32p_row21_traceSegment_018_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 151 15 16, g32p_row21_traceSegment_018_0151_0015, g32p_row21_traceSegment_018_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 121 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 121 30 31, g32p_row21_traceSegment_018_0121_0030, g32p_row21_traceSegment_018_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 182 15 15, g32p_row21_traceSegment_018_0182_0015, g32p_row21_traceSegment_018_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 212 15 16, g32p_row21_traceSegment_018_0212_0015, g32p_row21_traceSegment_018_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 182 30 31, g32p_row21_traceSegment_018_0182_0030, g32p_row21_traceSegment_018_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_018 121 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 121 61 61, g32p_row21_traceSegment_018_0121_0061, g32p_row21_traceSegment_018_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_018 0 243 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 0 121 122, g32p_row21_traceSegment_018_0000_0121, g32p_row21_traceSegment_018_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 258 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 243 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 243 15 15, g32p_row21_traceSegment_018_0243_0015, g32p_row21_traceSegment_018_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 273 15 15, g32p_row21_traceSegment_018_0273_0015, g32p_row21_traceSegment_018_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_018 243 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 243 30 30, g32p_row21_traceSegment_018_0243_0030, g32p_row21_traceSegment_018_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 303 15 15, g32p_row21_traceSegment_018_0303_0015, g32p_row21_traceSegment_018_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 333 15 16, g32p_row21_traceSegment_018_0333_0015, g32p_row21_traceSegment_018_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 303 30 31, g32p_row21_traceSegment_018_0303_0030, g32p_row21_traceSegment_018_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_018 243 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 243 60 61, g32p_row21_traceSegment_018_0243_0060, g32p_row21_traceSegment_018_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 364 15 15, g32p_row21_traceSegment_018_0364_0015, g32p_row21_traceSegment_018_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 394 15 16, g32p_row21_traceSegment_018_0394_0015, g32p_row21_traceSegment_018_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 364 30 31, g32p_row21_traceSegment_018_0364_0030, g32p_row21_traceSegment_018_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 425 15 15, g32p_row21_traceSegment_018_0425_0015, g32p_row21_traceSegment_018_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 455 15 16, g32p_row21_traceSegment_018_0455_0015, g32p_row21_traceSegment_018_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 425 30 31, g32p_row21_traceSegment_018_0425_0030, g32p_row21_traceSegment_018_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_018 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 364 61 61, g32p_row21_traceSegment_018_0364_0061, g32p_row21_traceSegment_018_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_018 243 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 243 121 122, g32p_row21_traceSegment_018_0243_0121, g32p_row21_traceSegment_018_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_018 0 486 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 0 243 243, g32p_row21_traceSegment_018_0000_0243, g32p_row21_traceSegment_018_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 486 15 15, g32p_row21_traceSegment_018_0486_0015, g32p_row21_traceSegment_018_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 516 15 15, g32p_row21_traceSegment_018_0516_0015, g32p_row21_traceSegment_018_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_018 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 486 30 30, g32p_row21_traceSegment_018_0486_0030, g32p_row21_traceSegment_018_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 546 15 15, g32p_row21_traceSegment_018_0546_0015, g32p_row21_traceSegment_018_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 576 15 16, g32p_row21_traceSegment_018_0576_0015, g32p_row21_traceSegment_018_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 546 30 31, g32p_row21_traceSegment_018_0546_0030, g32p_row21_traceSegment_018_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_018 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 486 60 61, g32p_row21_traceSegment_018_0486_0060, g32p_row21_traceSegment_018_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 607 15 15, g32p_row21_traceSegment_018_0607_0015, g32p_row21_traceSegment_018_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 637 15 16, g32p_row21_traceSegment_018_0637_0015, g32p_row21_traceSegment_018_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 607 30 31, g32p_row21_traceSegment_018_0607_0030, g32p_row21_traceSegment_018_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 683 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 668 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 668 15 15, g32p_row21_traceSegment_018_0668_0015, g32p_row21_traceSegment_018_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 698 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 698 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 698 15 16, g32p_row21_traceSegment_018_0698_0015, g32p_row21_traceSegment_018_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 668 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 668 30 31, g32p_row21_traceSegment_018_0668_0030, g32p_row21_traceSegment_018_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_018 607 122 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 607 61 61, g32p_row21_traceSegment_018_0607_0061, g32p_row21_traceSegment_018_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_018 486 243 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 486 121 122, g32p_row21_traceSegment_018_0486_0121, g32p_row21_traceSegment_018_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 729 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 744 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 729 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 729 15 15, g32p_row21_traceSegment_018_0729_0015, g32p_row21_traceSegment_018_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 759 15 15, g32p_row21_traceSegment_018_0759_0015, g32p_row21_traceSegment_018_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_018 729 60 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 729 30 30, g32p_row21_traceSegment_018_0729_0030, g32p_row21_traceSegment_018_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 789 15 15, g32p_row21_traceSegment_018_0789_0015, g32p_row21_traceSegment_018_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 819 15 16, g32p_row21_traceSegment_018_0819_0015, g32p_row21_traceSegment_018_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 789 30 31, g32p_row21_traceSegment_018_0789_0030, g32p_row21_traceSegment_018_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_018 729 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 729 60 61, g32p_row21_traceSegment_018_0729_0060, g32p_row21_traceSegment_018_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 850 15 15, g32p_row21_traceSegment_018_0850_0015, g32p_row21_traceSegment_018_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 895 16 = [3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 880 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 880 15 16, g32p_row21_traceSegment_018_0880_0015, g32p_row21_traceSegment_018_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 850 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 850 30 31, g32p_row21_traceSegment_018_0850_0030, g32p_row21_traceSegment_018_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 911 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 926 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_018 911 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 911 15 15, g32p_row21_traceSegment_018_0911_0015, g32p_row21_traceSegment_018_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_018 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_018 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_018_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_018 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 941 15 16, g32p_row21_traceSegment_018_0941_0015, g32p_row21_traceSegment_018_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_018 911 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 911 30 31, g32p_row21_traceSegment_018_0911_0030, g32p_row21_traceSegment_018_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_018 850 122 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 850 61 61, g32p_row21_traceSegment_018_0850_0061, g32p_row21_traceSegment_018_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_018 729 243 = [9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 729 121 122, g32p_row21_traceSegment_018_0729_0121, g32p_row21_traceSegment_018_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_018 486 486 = [12] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 486 243 243, g32p_row21_traceSegment_018_0486_0243, g32p_row21_traceSegment_018_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_018_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_018 0 972 = [18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_018 0 486 486, g32p_row21_traceSegment_018_0000_0486, g32p_row21_traceSegment_018_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 18 = [18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_018_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_019 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 19 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_019_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 0 15 15, g32p_row21_traceSegment_019_0000_0015, g32p_row21_traceSegment_019_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 30 15 15, g32p_row21_traceSegment_019_0030_0015, g32p_row21_traceSegment_019_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_019 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 0 30 30, g32p_row21_traceSegment_019_0000_0030, g32p_row21_traceSegment_019_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 60 15 15, g32p_row21_traceSegment_019_0060_0015, g32p_row21_traceSegment_019_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 90 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 105 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 90 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 90 15 16, g32p_row21_traceSegment_019_0090_0015, g32p_row21_traceSegment_019_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 60 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 60 30 31, g32p_row21_traceSegment_019_0060_0030, g32p_row21_traceSegment_019_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_019 0 121 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 0 60 61, g32p_row21_traceSegment_019_0000_0060, g32p_row21_traceSegment_019_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 121 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 136 15 = [2, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 121 30 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 121 15 15, g32p_row21_traceSegment_019_0121_0015, g32p_row21_traceSegment_019_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 151 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 151 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 151 15 16, g32p_row21_traceSegment_019_0151_0015, g32p_row21_traceSegment_019_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 121 61 = [3, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 121 30 31, g32p_row21_traceSegment_019_0121_0030, g32p_row21_traceSegment_019_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 182 15 15, g32p_row21_traceSegment_019_0182_0015, g32p_row21_traceSegment_019_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 212 15 16, g32p_row21_traceSegment_019_0212_0015, g32p_row21_traceSegment_019_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 182 30 31, g32p_row21_traceSegment_019_0182_0030, g32p_row21_traceSegment_019_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_019 121 122 = [3, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 121 61 61, g32p_row21_traceSegment_019_0121_0061, g32p_row21_traceSegment_019_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_019 0 243 = [3, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 0 121 122, g32p_row21_traceSegment_019_0000_0121, g32p_row21_traceSegment_019_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 243 15 15, g32p_row21_traceSegment_019_0243_0015, g32p_row21_traceSegment_019_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 273 15 15, g32p_row21_traceSegment_019_0273_0015, g32p_row21_traceSegment_019_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_019 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 243 30 30, g32p_row21_traceSegment_019_0243_0030, g32p_row21_traceSegment_019_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 303 15 15, g32p_row21_traceSegment_019_0303_0015, g32p_row21_traceSegment_019_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 333 15 16, g32p_row21_traceSegment_019_0333_0015, g32p_row21_traceSegment_019_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 303 30 31, g32p_row21_traceSegment_019_0303_0030, g32p_row21_traceSegment_019_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_019 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 243 60 61, g32p_row21_traceSegment_019_0243_0060, g32p_row21_traceSegment_019_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 364 15 15, g32p_row21_traceSegment_019_0364_0015, g32p_row21_traceSegment_019_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 394 15 16, g32p_row21_traceSegment_019_0394_0015, g32p_row21_traceSegment_019_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 364 30 31, g32p_row21_traceSegment_019_0364_0030, g32p_row21_traceSegment_019_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 425 15 15, g32p_row21_traceSegment_019_0425_0015, g32p_row21_traceSegment_019_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 455 15 16, g32p_row21_traceSegment_019_0455_0015, g32p_row21_traceSegment_019_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 425 30 31, g32p_row21_traceSegment_019_0425_0030, g32p_row21_traceSegment_019_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_019 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 364 61 61, g32p_row21_traceSegment_019_0364_0061, g32p_row21_traceSegment_019_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_019 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 243 121 122, g32p_row21_traceSegment_019_0243_0121, g32p_row21_traceSegment_019_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_019 0 486 = [3, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 0 243 243, g32p_row21_traceSegment_019_0000_0243, g32p_row21_traceSegment_019_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 486 15 15, g32p_row21_traceSegment_019_0486_0015, g32p_row21_traceSegment_019_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 516 15 15, g32p_row21_traceSegment_019_0516_0015, g32p_row21_traceSegment_019_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_019 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 486 30 30, g32p_row21_traceSegment_019_0486_0030, g32p_row21_traceSegment_019_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 546 15 15, g32p_row21_traceSegment_019_0546_0015, g32p_row21_traceSegment_019_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 576 15 16, g32p_row21_traceSegment_019_0576_0015, g32p_row21_traceSegment_019_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 546 30 31, g32p_row21_traceSegment_019_0546_0030, g32p_row21_traceSegment_019_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_019 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 486 60 61, g32p_row21_traceSegment_019_0486_0060, g32p_row21_traceSegment_019_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 607 15 15, g32p_row21_traceSegment_019_0607_0015, g32p_row21_traceSegment_019_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 637 15 16, g32p_row21_traceSegment_019_0637_0015, g32p_row21_traceSegment_019_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 607 30 31, g32p_row21_traceSegment_019_0607_0030, g32p_row21_traceSegment_019_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 668 15 = [1, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 683 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 668 30 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 668 15 15, g32p_row21_traceSegment_019_0668_0015, g32p_row21_traceSegment_019_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 698 15 = [1, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 713 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 698 31 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 698 15 16, g32p_row21_traceSegment_019_0698_0015, g32p_row21_traceSegment_019_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 668 61 = [4, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 668 30 31, g32p_row21_traceSegment_019_0668_0030, g32p_row21_traceSegment_019_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_019 607 122 = [4, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 607 61 61, g32p_row21_traceSegment_019_0607_0061, g32p_row21_traceSegment_019_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_019 486 243 = [4, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 486 121 122, g32p_row21_traceSegment_019_0486_0121, g32p_row21_traceSegment_019_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 744 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 729 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 729 15 15, g32p_row21_traceSegment_019_0729_0015, g32p_row21_traceSegment_019_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 759 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 759 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 759 15 15, g32p_row21_traceSegment_019_0759_0015, g32p_row21_traceSegment_019_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_019 729 60 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 729 30 30, g32p_row21_traceSegment_019_0729_0030, g32p_row21_traceSegment_019_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 789 15 15, g32p_row21_traceSegment_019_0789_0015, g32p_row21_traceSegment_019_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 819 15 16, g32p_row21_traceSegment_019_0819_0015, g32p_row21_traceSegment_019_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 789 30 31, g32p_row21_traceSegment_019_0789_0030, g32p_row21_traceSegment_019_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_019 729 121 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 729 60 61, g32p_row21_traceSegment_019_0729_0060, g32p_row21_traceSegment_019_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 850 15 15, g32p_row21_traceSegment_019_0850_0015, g32p_row21_traceSegment_019_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 880 15 16, g32p_row21_traceSegment_019_0880_0015, g32p_row21_traceSegment_019_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 850 30 31, g32p_row21_traceSegment_019_0850_0030, g32p_row21_traceSegment_019_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_019 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 911 15 15, g32p_row21_traceSegment_019_0911_0015, g32p_row21_traceSegment_019_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_019 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_019 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_019_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_019 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 941 15 16, g32p_row21_traceSegment_019_0941_0015, g32p_row21_traceSegment_019_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_019 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 911 30 31, g32p_row21_traceSegment_019_0911_0030, g32p_row21_traceSegment_019_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_019 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 850 61 61, g32p_row21_traceSegment_019_0850_0061, g32p_row21_traceSegment_019_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_019 729 243 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 729 121 122, g32p_row21_traceSegment_019_0729_0121, g32p_row21_traceSegment_019_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_019 486 486 = [6, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 486 243 243, g32p_row21_traceSegment_019_0486_0243, g32p_row21_traceSegment_019_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_019_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_019 0 972 = [9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_019 0 486 486, g32p_row21_traceSegment_019_0000_0486, g32p_row21_traceSegment_019_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 19 = [9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_019_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_023 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 23 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_023_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 0 15 15, g32p_row21_traceSegment_023_0000_0015, g32p_row21_traceSegment_023_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 30 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 30 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 30 15 15, g32p_row21_traceSegment_023_0030_0015, g32p_row21_traceSegment_023_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_023 0 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 0 30 30, g32p_row21_traceSegment_023_0000_0030, g32p_row21_traceSegment_023_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 60 15 15, g32p_row21_traceSegment_023_0060_0015, g32p_row21_traceSegment_023_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 90 15 16, g32p_row21_traceSegment_023_0090_0015, g32p_row21_traceSegment_023_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 60 30 31, g32p_row21_traceSegment_023_0060_0030, g32p_row21_traceSegment_023_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_023 0 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 0 60 61, g32p_row21_traceSegment_023_0000_0060, g32p_row21_traceSegment_023_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 121 15 15, g32p_row21_traceSegment_023_0121_0015, g32p_row21_traceSegment_023_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 151 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 151 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 151 15 16, g32p_row21_traceSegment_023_0151_0015, g32p_row21_traceSegment_023_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 121 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 121 30 31, g32p_row21_traceSegment_023_0121_0030, g32p_row21_traceSegment_023_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 182 15 15, g32p_row21_traceSegment_023_0182_0015, g32p_row21_traceSegment_023_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 212 15 16, g32p_row21_traceSegment_023_0212_0015, g32p_row21_traceSegment_023_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 182 30 31, g32p_row21_traceSegment_023_0182_0030, g32p_row21_traceSegment_023_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_023 121 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 121 61 61, g32p_row21_traceSegment_023_0121_0061, g32p_row21_traceSegment_023_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_023 0 243 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 0 121 122, g32p_row21_traceSegment_023_0000_0121, g32p_row21_traceSegment_023_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 243 15 15, g32p_row21_traceSegment_023_0243_0015, g32p_row21_traceSegment_023_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 273 15 15, g32p_row21_traceSegment_023_0273_0015, g32p_row21_traceSegment_023_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_023 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 243 30 30, g32p_row21_traceSegment_023_0243_0030, g32p_row21_traceSegment_023_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 318 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 303 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 303 15 15, g32p_row21_traceSegment_023_0303_0015, g32p_row21_traceSegment_023_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 333 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 348 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 333 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 333 15 16, g32p_row21_traceSegment_023_0333_0015, g32p_row21_traceSegment_023_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 303 61 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 303 30 31, g32p_row21_traceSegment_023_0303_0030, g32p_row21_traceSegment_023_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_023 243 121 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 243 60 61, g32p_row21_traceSegment_023_0243_0060, g32p_row21_traceSegment_023_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 379 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 364 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 364 15 15, g32p_row21_traceSegment_023_0364_0015, g32p_row21_traceSegment_023_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 409 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 394 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 394 15 16, g32p_row21_traceSegment_023_0394_0015, g32p_row21_traceSegment_023_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 364 61 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 364 30 31, g32p_row21_traceSegment_023_0364_0030, g32p_row21_traceSegment_023_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 425 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 440 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 425 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 425 15 15, g32p_row21_traceSegment_023_0425_0015, g32p_row21_traceSegment_023_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 455 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 470 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 455 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 455 15 16, g32p_row21_traceSegment_023_0455_0015, g32p_row21_traceSegment_023_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 425 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 425 30 31, g32p_row21_traceSegment_023_0425_0030, g32p_row21_traceSegment_023_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_023 364 122 = [1, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 364 61 61, g32p_row21_traceSegment_023_0364_0061, g32p_row21_traceSegment_023_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_023 243 243 = [5, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 243 121 122, g32p_row21_traceSegment_023_0243_0121, g32p_row21_traceSegment_023_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_023 0 486 = [7, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 0 243 243, g32p_row21_traceSegment_023_0000_0243, g32p_row21_traceSegment_023_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 486 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 486 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 486 15 15, g32p_row21_traceSegment_023_0486_0015, g32p_row21_traceSegment_023_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 516 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 516 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 516 15 15, g32p_row21_traceSegment_023_0516_0015, g32p_row21_traceSegment_023_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_023 486 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 486 30 30, g32p_row21_traceSegment_023_0486_0030, g32p_row21_traceSegment_023_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 546 15 15, g32p_row21_traceSegment_023_0546_0015, g32p_row21_traceSegment_023_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 576 15 16, g32p_row21_traceSegment_023_0576_0015, g32p_row21_traceSegment_023_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 546 30 31, g32p_row21_traceSegment_023_0546_0030, g32p_row21_traceSegment_023_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_023 486 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 486 60 61, g32p_row21_traceSegment_023_0486_0060, g32p_row21_traceSegment_023_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 607 15 15, g32p_row21_traceSegment_023_0607_0015, g32p_row21_traceSegment_023_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 637 15 16, g32p_row21_traceSegment_023_0637_0015, g32p_row21_traceSegment_023_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 607 30 31, g32p_row21_traceSegment_023_0607_0030, g32p_row21_traceSegment_023_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 668 15 15, g32p_row21_traceSegment_023_0668_0015, g32p_row21_traceSegment_023_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 698 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 713 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 698 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 698 15 16, g32p_row21_traceSegment_023_0698_0015, g32p_row21_traceSegment_023_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 668 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 668 30 31, g32p_row21_traceSegment_023_0668_0030, g32p_row21_traceSegment_023_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_023 607 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 607 61 61, g32p_row21_traceSegment_023_0607_0061, g32p_row21_traceSegment_023_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_023 486 243 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 486 121 122, g32p_row21_traceSegment_023_0486_0121, g32p_row21_traceSegment_023_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 729 15 15, g32p_row21_traceSegment_023_0729_0015, g32p_row21_traceSegment_023_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 759 15 15, g32p_row21_traceSegment_023_0759_0015, g32p_row21_traceSegment_023_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_023 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 729 30 30, g32p_row21_traceSegment_023_0729_0030, g32p_row21_traceSegment_023_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 789 15 15, g32p_row21_traceSegment_023_0789_0015, g32p_row21_traceSegment_023_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 819 15 16, g32p_row21_traceSegment_023_0819_0015, g32p_row21_traceSegment_023_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 789 30 31, g32p_row21_traceSegment_023_0789_0030, g32p_row21_traceSegment_023_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_023 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 729 60 61, g32p_row21_traceSegment_023_0729_0060, g32p_row21_traceSegment_023_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 850 15 15, g32p_row21_traceSegment_023_0850_0015, g32p_row21_traceSegment_023_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 880 15 16, g32p_row21_traceSegment_023_0880_0015, g32p_row21_traceSegment_023_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 850 30 31, g32p_row21_traceSegment_023_0850_0030, g32p_row21_traceSegment_023_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 926 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_023 911 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 911 15 15, g32p_row21_traceSegment_023_0911_0015, g32p_row21_traceSegment_023_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_023 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_023 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_023_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_023 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 941 15 16, g32p_row21_traceSegment_023_0941_0015, g32p_row21_traceSegment_023_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_023 911 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 911 30 31, g32p_row21_traceSegment_023_0911_0030, g32p_row21_traceSegment_023_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_023 850 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 850 61 61, g32p_row21_traceSegment_023_0850_0061, g32p_row21_traceSegment_023_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_023 729 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 729 121 122, g32p_row21_traceSegment_023_0729_0121, g32p_row21_traceSegment_023_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_023 486 486 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 486 243 243, g32p_row21_traceSegment_023_0486_0243, g32p_row21_traceSegment_023_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_023_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_023 0 972 = [9, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_023 0 486 486, g32p_row21_traceSegment_023_0000_0486, g32p_row21_traceSegment_023_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 23 = [9, 0, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_023_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row21_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 10) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 10) (g32p_literalTraceValue 20 10)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_010]
  decide +kernel

theorem g32p_row21_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 11) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 11) (g32p_literalTraceValue 20 11)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row21_traceCoefficients_011]
  decide +kernel

theorem g32p_row21_tracePolynomial_012 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 12) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 12) (g32p_literalTraceValue 20 12)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_012]
  decide +kernel

theorem g32p_row21_tracePolynomial_014 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 14) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 14) (g32p_literalTraceValue 20 14)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_014]
  decide +kernel

theorem g32p_row21_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 15) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 15) (g32p_literalTraceValue 20 15)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_015]
  decide +kernel

theorem g32p_row21_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 18) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 18) (g32p_literalTraceValue 20 18)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_018]
  decide +kernel

theorem g32p_row21_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 19) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 19) (g32p_literalTraceValue 20 19)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_019]
  decide +kernel

theorem g32p_row21_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 23) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 23) (g32p_literalTraceValue 20 23)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_023]
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

private def g32p_row21_traceSegment_024 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 24 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_024_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 0 15 15, g32p_row21_traceSegment_024_0000_0015, g32p_row21_traceSegment_024_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 30 15 15, g32p_row21_traceSegment_024_0030_0015, g32p_row21_traceSegment_024_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_024 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 0 30 30, g32p_row21_traceSegment_024_0000_0030, g32p_row21_traceSegment_024_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 60 15 15, g32p_row21_traceSegment_024_0060_0015, g32p_row21_traceSegment_024_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 90 15 16, g32p_row21_traceSegment_024_0090_0015, g32p_row21_traceSegment_024_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 60 30 31, g32p_row21_traceSegment_024_0060_0030, g32p_row21_traceSegment_024_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_024 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 0 60 61, g32p_row21_traceSegment_024_0000_0060, g32p_row21_traceSegment_024_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 121 15 15, g32p_row21_traceSegment_024_0121_0015, g32p_row21_traceSegment_024_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 151 15 16, g32p_row21_traceSegment_024_0151_0015, g32p_row21_traceSegment_024_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 121 30 31, g32p_row21_traceSegment_024_0121_0030, g32p_row21_traceSegment_024_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 182 15 15, g32p_row21_traceSegment_024_0182_0015, g32p_row21_traceSegment_024_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 212 15 16, g32p_row21_traceSegment_024_0212_0015, g32p_row21_traceSegment_024_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 182 30 31, g32p_row21_traceSegment_024_0182_0030, g32p_row21_traceSegment_024_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_024 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 121 61 61, g32p_row21_traceSegment_024_0121_0061, g32p_row21_traceSegment_024_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_024 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 0 121 122, g32p_row21_traceSegment_024_0000_0121, g32p_row21_traceSegment_024_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 243 15 15, g32p_row21_traceSegment_024_0243_0015, g32p_row21_traceSegment_024_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 273 15 15, g32p_row21_traceSegment_024_0273_0015, g32p_row21_traceSegment_024_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_024 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 243 30 30, g32p_row21_traceSegment_024_0243_0030, g32p_row21_traceSegment_024_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 303 15 15, g32p_row21_traceSegment_024_0303_0015, g32p_row21_traceSegment_024_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 333 15 16, g32p_row21_traceSegment_024_0333_0015, g32p_row21_traceSegment_024_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 303 30 31, g32p_row21_traceSegment_024_0303_0030, g32p_row21_traceSegment_024_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_024 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 243 60 61, g32p_row21_traceSegment_024_0243_0060, g32p_row21_traceSegment_024_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 364 15 15, g32p_row21_traceSegment_024_0364_0015, g32p_row21_traceSegment_024_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 394 15 16, g32p_row21_traceSegment_024_0394_0015, g32p_row21_traceSegment_024_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 364 30 31, g32p_row21_traceSegment_024_0364_0030, g32p_row21_traceSegment_024_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 425 15 15, g32p_row21_traceSegment_024_0425_0015, g32p_row21_traceSegment_024_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 455 15 16, g32p_row21_traceSegment_024_0455_0015, g32p_row21_traceSegment_024_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 425 30 31, g32p_row21_traceSegment_024_0425_0030, g32p_row21_traceSegment_024_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_024 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 364 61 61, g32p_row21_traceSegment_024_0364_0061, g32p_row21_traceSegment_024_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_024 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 243 121 122, g32p_row21_traceSegment_024_0243_0121, g32p_row21_traceSegment_024_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_024 0 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 0 243 243, g32p_row21_traceSegment_024_0000_0243, g32p_row21_traceSegment_024_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 486 15 15, g32p_row21_traceSegment_024_0486_0015, g32p_row21_traceSegment_024_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 516 15 15, g32p_row21_traceSegment_024_0516_0015, g32p_row21_traceSegment_024_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_024 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 486 30 30, g32p_row21_traceSegment_024_0486_0030, g32p_row21_traceSegment_024_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 546 15 15, g32p_row21_traceSegment_024_0546_0015, g32p_row21_traceSegment_024_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 576 15 16, g32p_row21_traceSegment_024_0576_0015, g32p_row21_traceSegment_024_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 546 30 31, g32p_row21_traceSegment_024_0546_0030, g32p_row21_traceSegment_024_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_024 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 486 60 61, g32p_row21_traceSegment_024_0486_0060, g32p_row21_traceSegment_024_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 607 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 622 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 607 30 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 607 15 15, g32p_row21_traceSegment_024_0607_0015, g32p_row21_traceSegment_024_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 637 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 652 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 637 31 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 637 15 16, g32p_row21_traceSegment_024_0637_0015, g32p_row21_traceSegment_024_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 607 61 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 607 30 31, g32p_row21_traceSegment_024_0607_0030, g32p_row21_traceSegment_024_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 668 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 668 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 668 15 15, g32p_row21_traceSegment_024_0668_0015, g32p_row21_traceSegment_024_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 698 15 16, g32p_row21_traceSegment_024_0698_0015, g32p_row21_traceSegment_024_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 668 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 668 30 31, g32p_row21_traceSegment_024_0668_0030, g32p_row21_traceSegment_024_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_024 607 122 = [0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 607 61 61, g32p_row21_traceSegment_024_0607_0061, g32p_row21_traceSegment_024_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_024 486 243 = [0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 486 121 122, g32p_row21_traceSegment_024_0486_0121, g32p_row21_traceSegment_024_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 729 15 15, g32p_row21_traceSegment_024_0729_0015, g32p_row21_traceSegment_024_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 759 15 15, g32p_row21_traceSegment_024_0759_0015, g32p_row21_traceSegment_024_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_024 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 729 30 30, g32p_row21_traceSegment_024_0729_0030, g32p_row21_traceSegment_024_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 789 15 15, g32p_row21_traceSegment_024_0789_0015, g32p_row21_traceSegment_024_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 819 15 16, g32p_row21_traceSegment_024_0819_0015, g32p_row21_traceSegment_024_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 789 30 31, g32p_row21_traceSegment_024_0789_0030, g32p_row21_traceSegment_024_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_024 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 729 60 61, g32p_row21_traceSegment_024_0729_0060, g32p_row21_traceSegment_024_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 850 15 15, g32p_row21_traceSegment_024_0850_0015, g32p_row21_traceSegment_024_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 880 15 16, g32p_row21_traceSegment_024_0880_0015, g32p_row21_traceSegment_024_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 850 30 31, g32p_row21_traceSegment_024_0850_0030, g32p_row21_traceSegment_024_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_024 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 911 15 15, g32p_row21_traceSegment_024_0911_0015, g32p_row21_traceSegment_024_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_024 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_024 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_024_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_024 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 941 15 16, g32p_row21_traceSegment_024_0941_0015, g32p_row21_traceSegment_024_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_024 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 911 30 31, g32p_row21_traceSegment_024_0911_0030, g32p_row21_traceSegment_024_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_024 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 850 61 61, g32p_row21_traceSegment_024_0850_0061, g32p_row21_traceSegment_024_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_024 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 729 121 122, g32p_row21_traceSegment_024_0729_0121, g32p_row21_traceSegment_024_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_024 486 486 = [0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 486 243 243, g32p_row21_traceSegment_024_0486_0243, g32p_row21_traceSegment_024_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_024_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_024 0 972 = [0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_024 0 486 486, g32p_row21_traceSegment_024_0000_0486, g32p_row21_traceSegment_024_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 24 = [0, 3, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_024_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_025 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 25 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_025_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 0 15 15, g32p_row21_traceSegment_025_0000_0015, g32p_row21_traceSegment_025_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 30 15 15, g32p_row21_traceSegment_025_0030_0015, g32p_row21_traceSegment_025_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_025 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 0 30 30, g32p_row21_traceSegment_025_0000_0030, g32p_row21_traceSegment_025_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 60 15 15, g32p_row21_traceSegment_025_0060_0015, g32p_row21_traceSegment_025_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 90 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 105 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 90 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 90 15 16, g32p_row21_traceSegment_025_0090_0015, g32p_row21_traceSegment_025_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 60 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 60 30 31, g32p_row21_traceSegment_025_0060_0030, g32p_row21_traceSegment_025_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_025 0 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 0 60 61, g32p_row21_traceSegment_025_0000_0060, g32p_row21_traceSegment_025_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 121 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 121 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 121 15 15, g32p_row21_traceSegment_025_0121_0015, g32p_row21_traceSegment_025_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 151 15 16, g32p_row21_traceSegment_025_0151_0015, g32p_row21_traceSegment_025_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 121 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 121 30 31, g32p_row21_traceSegment_025_0121_0030, g32p_row21_traceSegment_025_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 182 15 15, g32p_row21_traceSegment_025_0182_0015, g32p_row21_traceSegment_025_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 227 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 212 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 212 15 16, g32p_row21_traceSegment_025_0212_0015, g32p_row21_traceSegment_025_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 182 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 182 30 31, g32p_row21_traceSegment_025_0182_0030, g32p_row21_traceSegment_025_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_025 121 122 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 121 61 61, g32p_row21_traceSegment_025_0121_0061, g32p_row21_traceSegment_025_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_025 0 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 0 121 122, g32p_row21_traceSegment_025_0000_0121, g32p_row21_traceSegment_025_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 243 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 243 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 243 15 15, g32p_row21_traceSegment_025_0243_0015, g32p_row21_traceSegment_025_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 273 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 273 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 273 15 15, g32p_row21_traceSegment_025_0273_0015, g32p_row21_traceSegment_025_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_025 243 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 243 30 30, g32p_row21_traceSegment_025_0243_0030, g32p_row21_traceSegment_025_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 303 15 15, g32p_row21_traceSegment_025_0303_0015, g32p_row21_traceSegment_025_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 348 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 333 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 333 15 16, g32p_row21_traceSegment_025_0333_0015, g32p_row21_traceSegment_025_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 303 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 303 30 31, g32p_row21_traceSegment_025_0303_0030, g32p_row21_traceSegment_025_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_025 243 121 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 243 60 61, g32p_row21_traceSegment_025_0243_0060, g32p_row21_traceSegment_025_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 364 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 379 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 364 30 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 364 15 15, g32p_row21_traceSegment_025_0364_0015, g32p_row21_traceSegment_025_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 394 15 16, g32p_row21_traceSegment_025_0394_0015, g32p_row21_traceSegment_025_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 364 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 364 30 31, g32p_row21_traceSegment_025_0364_0030, g32p_row21_traceSegment_025_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 425 15 15, g32p_row21_traceSegment_025_0425_0015, g32p_row21_traceSegment_025_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 455 15 16, g32p_row21_traceSegment_025_0455_0015, g32p_row21_traceSegment_025_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 425 30 31, g32p_row21_traceSegment_025_0425_0030, g32p_row21_traceSegment_025_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_025 364 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 364 61 61, g32p_row21_traceSegment_025_0364_0061, g32p_row21_traceSegment_025_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_025 243 243 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 243 121 122, g32p_row21_traceSegment_025_0243_0121, g32p_row21_traceSegment_025_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_025 0 486 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 0 243 243, g32p_row21_traceSegment_025_0000_0243, g32p_row21_traceSegment_025_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 486 15 15, g32p_row21_traceSegment_025_0486_0015, g32p_row21_traceSegment_025_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 516 15 15, g32p_row21_traceSegment_025_0516_0015, g32p_row21_traceSegment_025_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_025 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 486 30 30, g32p_row21_traceSegment_025_0486_0030, g32p_row21_traceSegment_025_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 546 15 15, g32p_row21_traceSegment_025_0546_0015, g32p_row21_traceSegment_025_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 576 15 16, g32p_row21_traceSegment_025_0576_0015, g32p_row21_traceSegment_025_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 546 30 31, g32p_row21_traceSegment_025_0546_0030, g32p_row21_traceSegment_025_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_025 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 486 60 61, g32p_row21_traceSegment_025_0486_0060, g32p_row21_traceSegment_025_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 622 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 607 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 607 15 15, g32p_row21_traceSegment_025_0607_0015, g32p_row21_traceSegment_025_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 637 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 652 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 637 31 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 637 15 16, g32p_row21_traceSegment_025_0637_0015, g32p_row21_traceSegment_025_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 607 61 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 607 30 31, g32p_row21_traceSegment_025_0607_0030, g32p_row21_traceSegment_025_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 668 15 15, g32p_row21_traceSegment_025_0668_0015, g32p_row21_traceSegment_025_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 698 15 16, g32p_row21_traceSegment_025_0698_0015, g32p_row21_traceSegment_025_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 668 30 31, g32p_row21_traceSegment_025_0668_0030, g32p_row21_traceSegment_025_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_025 607 122 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 607 61 61, g32p_row21_traceSegment_025_0607_0061, g32p_row21_traceSegment_025_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_025 486 243 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 486 121 122, g32p_row21_traceSegment_025_0486_0121, g32p_row21_traceSegment_025_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 729 15 15, g32p_row21_traceSegment_025_0729_0015, g32p_row21_traceSegment_025_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 759 15 15, g32p_row21_traceSegment_025_0759_0015, g32p_row21_traceSegment_025_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_025 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 729 30 30, g32p_row21_traceSegment_025_0729_0030, g32p_row21_traceSegment_025_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 789 15 15, g32p_row21_traceSegment_025_0789_0015, g32p_row21_traceSegment_025_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 819 15 16, g32p_row21_traceSegment_025_0819_0015, g32p_row21_traceSegment_025_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 789 30 31, g32p_row21_traceSegment_025_0789_0030, g32p_row21_traceSegment_025_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_025 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 729 60 61, g32p_row21_traceSegment_025_0729_0060, g32p_row21_traceSegment_025_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 850 15 15, g32p_row21_traceSegment_025_0850_0015, g32p_row21_traceSegment_025_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 880 15 16, g32p_row21_traceSegment_025_0880_0015, g32p_row21_traceSegment_025_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 850 30 31, g32p_row21_traceSegment_025_0850_0030, g32p_row21_traceSegment_025_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_025 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 911 15 15, g32p_row21_traceSegment_025_0911_0015, g32p_row21_traceSegment_025_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_025 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_025 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_025_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_025 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 941 15 16, g32p_row21_traceSegment_025_0941_0015, g32p_row21_traceSegment_025_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_025 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 911 30 31, g32p_row21_traceSegment_025_0911_0030, g32p_row21_traceSegment_025_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_025 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 850 61 61, g32p_row21_traceSegment_025_0850_0061, g32p_row21_traceSegment_025_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_025 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 729 121 122, g32p_row21_traceSegment_025_0729_0121, g32p_row21_traceSegment_025_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_025 486 486 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 486 243 243, g32p_row21_traceSegment_025_0486_0243, g32p_row21_traceSegment_025_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_025_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_025 0 972 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_025 0 486 486, g32p_row21_traceSegment_025_0000_0486, g32p_row21_traceSegment_025_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 25 = [0, 0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_025_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_028 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 28 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_028_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 0 15 15, g32p_row21_traceSegment_028_0000_0015, g32p_row21_traceSegment_028_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 30 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 30 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 30 15 15, g32p_row21_traceSegment_028_0030_0015, g32p_row21_traceSegment_028_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_028 0 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 0 30 30, g32p_row21_traceSegment_028_0000_0030, g32p_row21_traceSegment_028_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 60 15 15, g32p_row21_traceSegment_028_0060_0015, g32p_row21_traceSegment_028_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 90 15 16, g32p_row21_traceSegment_028_0090_0015, g32p_row21_traceSegment_028_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 60 30 31, g32p_row21_traceSegment_028_0060_0030, g32p_row21_traceSegment_028_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_028 0 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 0 60 61, g32p_row21_traceSegment_028_0000_0060, g32p_row21_traceSegment_028_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 121 15 15, g32p_row21_traceSegment_028_0121_0015, g32p_row21_traceSegment_028_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 151 15 16, g32p_row21_traceSegment_028_0151_0015, g32p_row21_traceSegment_028_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 121 30 31, g32p_row21_traceSegment_028_0121_0030, g32p_row21_traceSegment_028_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 182 15 15, g32p_row21_traceSegment_028_0182_0015, g32p_row21_traceSegment_028_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 212 15 16, g32p_row21_traceSegment_028_0212_0015, g32p_row21_traceSegment_028_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 182 30 31, g32p_row21_traceSegment_028_0182_0030, g32p_row21_traceSegment_028_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_028 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 121 61 61, g32p_row21_traceSegment_028_0121_0061, g32p_row21_traceSegment_028_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_028 0 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 0 121 122, g32p_row21_traceSegment_028_0000_0121, g32p_row21_traceSegment_028_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 243 15 15, g32p_row21_traceSegment_028_0243_0015, g32p_row21_traceSegment_028_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 273 15 15, g32p_row21_traceSegment_028_0273_0015, g32p_row21_traceSegment_028_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_028 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 243 30 30, g32p_row21_traceSegment_028_0243_0030, g32p_row21_traceSegment_028_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 303 15 15, g32p_row21_traceSegment_028_0303_0015, g32p_row21_traceSegment_028_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 333 15 16, g32p_row21_traceSegment_028_0333_0015, g32p_row21_traceSegment_028_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 303 30 31, g32p_row21_traceSegment_028_0303_0030, g32p_row21_traceSegment_028_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_028 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 243 60 61, g32p_row21_traceSegment_028_0243_0060, g32p_row21_traceSegment_028_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 364 15 15, g32p_row21_traceSegment_028_0364_0015, g32p_row21_traceSegment_028_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 394 15 16, g32p_row21_traceSegment_028_0394_0015, g32p_row21_traceSegment_028_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 364 30 31, g32p_row21_traceSegment_028_0364_0030, g32p_row21_traceSegment_028_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 425 15 15, g32p_row21_traceSegment_028_0425_0015, g32p_row21_traceSegment_028_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 455 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 455 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 455 15 16, g32p_row21_traceSegment_028_0455_0015, g32p_row21_traceSegment_028_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 425 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 425 30 31, g32p_row21_traceSegment_028_0425_0030, g32p_row21_traceSegment_028_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_028 364 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 364 61 61, g32p_row21_traceSegment_028_0364_0061, g32p_row21_traceSegment_028_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_028 243 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 243 121 122, g32p_row21_traceSegment_028_0243_0121, g32p_row21_traceSegment_028_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_028 0 486 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 0 243 243, g32p_row21_traceSegment_028_0000_0243, g32p_row21_traceSegment_028_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 486 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 486 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 486 15 15, g32p_row21_traceSegment_028_0486_0015, g32p_row21_traceSegment_028_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 516 15 15, g32p_row21_traceSegment_028_0516_0015, g32p_row21_traceSegment_028_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_028 486 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 486 30 30, g32p_row21_traceSegment_028_0486_0030, g32p_row21_traceSegment_028_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 546 15 15, g32p_row21_traceSegment_028_0546_0015, g32p_row21_traceSegment_028_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 576 15 16, g32p_row21_traceSegment_028_0576_0015, g32p_row21_traceSegment_028_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 546 30 31, g32p_row21_traceSegment_028_0546_0030, g32p_row21_traceSegment_028_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_028 486 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 486 60 61, g32p_row21_traceSegment_028_0486_0060, g32p_row21_traceSegment_028_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 607 15 15, g32p_row21_traceSegment_028_0607_0015, g32p_row21_traceSegment_028_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 637 15 16, g32p_row21_traceSegment_028_0637_0015, g32p_row21_traceSegment_028_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 607 30 31, g32p_row21_traceSegment_028_0607_0030, g32p_row21_traceSegment_028_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 668 15 15, g32p_row21_traceSegment_028_0668_0015, g32p_row21_traceSegment_028_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 698 15 16, g32p_row21_traceSegment_028_0698_0015, g32p_row21_traceSegment_028_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 668 30 31, g32p_row21_traceSegment_028_0668_0030, g32p_row21_traceSegment_028_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_028 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 607 61 61, g32p_row21_traceSegment_028_0607_0061, g32p_row21_traceSegment_028_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_028 486 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 486 121 122, g32p_row21_traceSegment_028_0486_0121, g32p_row21_traceSegment_028_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 729 15 15, g32p_row21_traceSegment_028_0729_0015, g32p_row21_traceSegment_028_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 759 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 759 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 759 15 15, g32p_row21_traceSegment_028_0759_0015, g32p_row21_traceSegment_028_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_028 729 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 729 30 30, g32p_row21_traceSegment_028_0729_0030, g32p_row21_traceSegment_028_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 789 15 15, g32p_row21_traceSegment_028_0789_0015, g32p_row21_traceSegment_028_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 819 15 16, g32p_row21_traceSegment_028_0819_0015, g32p_row21_traceSegment_028_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 789 30 31, g32p_row21_traceSegment_028_0789_0030, g32p_row21_traceSegment_028_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_028 729 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 729 60 61, g32p_row21_traceSegment_028_0729_0060, g32p_row21_traceSegment_028_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 850 15 15, g32p_row21_traceSegment_028_0850_0015, g32p_row21_traceSegment_028_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 880 15 16, g32p_row21_traceSegment_028_0880_0015, g32p_row21_traceSegment_028_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 850 30 31, g32p_row21_traceSegment_028_0850_0030, g32p_row21_traceSegment_028_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_028 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 911 15 15, g32p_row21_traceSegment_028_0911_0015, g32p_row21_traceSegment_028_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_028 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_028 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_028_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_028 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 941 15 16, g32p_row21_traceSegment_028_0941_0015, g32p_row21_traceSegment_028_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_028 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 911 30 31, g32p_row21_traceSegment_028_0911_0030, g32p_row21_traceSegment_028_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_028 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 850 61 61, g32p_row21_traceSegment_028_0850_0061, g32p_row21_traceSegment_028_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_028 729 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 729 121 122, g32p_row21_traceSegment_028_0729_0121, g32p_row21_traceSegment_028_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_028 486 486 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 486 243 243, g32p_row21_traceSegment_028_0486_0243, g32p_row21_traceSegment_028_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_028_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_028 0 972 = [3, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_028 0 486 486, g32p_row21_traceSegment_028_0000_0486, g32p_row21_traceSegment_028_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 28 = [3, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_028_0000_0972

end HodgeLean.Foundations.Program

end
end
