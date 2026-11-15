import HodgeLean.Foundations.Program.G32PropFourSixPacked0382
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0386
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0383
import HodgeLean.Foundations.Program.G32PropFourSixPacked0384
import HodgeLean.Foundations.Program.G32PropFourSixPacked0385
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_095 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 95 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_095_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 0 15 15, g32p_row21_traceSegment_095_0000_0015, g32p_row21_traceSegment_095_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 30 15 15, g32p_row21_traceSegment_095_0030_0015, g32p_row21_traceSegment_095_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_095 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 0 30 30, g32p_row21_traceSegment_095_0000_0030, g32p_row21_traceSegment_095_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 60 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 60 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 60 15 15, g32p_row21_traceSegment_095_0060_0015, g32p_row21_traceSegment_095_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 90 15 16, g32p_row21_traceSegment_095_0090_0015, g32p_row21_traceSegment_095_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 60 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 60 30 31, g32p_row21_traceSegment_095_0060_0030, g32p_row21_traceSegment_095_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_095 0 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 0 60 61, g32p_row21_traceSegment_095_0000_0060, g32p_row21_traceSegment_095_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 121 15 15, g32p_row21_traceSegment_095_0121_0015, g32p_row21_traceSegment_095_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 151 15 16, g32p_row21_traceSegment_095_0151_0015, g32p_row21_traceSegment_095_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 121 30 31, g32p_row21_traceSegment_095_0121_0030, g32p_row21_traceSegment_095_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 182 15 15, g32p_row21_traceSegment_095_0182_0015, g32p_row21_traceSegment_095_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 212 15 16, g32p_row21_traceSegment_095_0212_0015, g32p_row21_traceSegment_095_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 182 30 31, g32p_row21_traceSegment_095_0182_0030, g32p_row21_traceSegment_095_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_095 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 121 61 61, g32p_row21_traceSegment_095_0121_0061, g32p_row21_traceSegment_095_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_095 0 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 0 121 122, g32p_row21_traceSegment_095_0000_0121, g32p_row21_traceSegment_095_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 243 15 15, g32p_row21_traceSegment_095_0243_0015, g32p_row21_traceSegment_095_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 273 15 15, g32p_row21_traceSegment_095_0273_0015, g32p_row21_traceSegment_095_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_095 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 243 30 30, g32p_row21_traceSegment_095_0243_0030, g32p_row21_traceSegment_095_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 303 15 15, g32p_row21_traceSegment_095_0303_0015, g32p_row21_traceSegment_095_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 333 15 16, g32p_row21_traceSegment_095_0333_0015, g32p_row21_traceSegment_095_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 303 30 31, g32p_row21_traceSegment_095_0303_0030, g32p_row21_traceSegment_095_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_095 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 243 60 61, g32p_row21_traceSegment_095_0243_0060, g32p_row21_traceSegment_095_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 364 15 15, g32p_row21_traceSegment_095_0364_0015, g32p_row21_traceSegment_095_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 394 15 16, g32p_row21_traceSegment_095_0394_0015, g32p_row21_traceSegment_095_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 364 30 31, g32p_row21_traceSegment_095_0364_0030, g32p_row21_traceSegment_095_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 425 15 15, g32p_row21_traceSegment_095_0425_0015, g32p_row21_traceSegment_095_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 455 15 16, g32p_row21_traceSegment_095_0455_0015, g32p_row21_traceSegment_095_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 425 30 31, g32p_row21_traceSegment_095_0425_0030, g32p_row21_traceSegment_095_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_095 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 364 61 61, g32p_row21_traceSegment_095_0364_0061, g32p_row21_traceSegment_095_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_095 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 243 121 122, g32p_row21_traceSegment_095_0243_0121, g32p_row21_traceSegment_095_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_095 0 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 0 243 243, g32p_row21_traceSegment_095_0000_0243, g32p_row21_traceSegment_095_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 486 15 15, g32p_row21_traceSegment_095_0486_0015, g32p_row21_traceSegment_095_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 516 15 15, g32p_row21_traceSegment_095_0516_0015, g32p_row21_traceSegment_095_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_095 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 486 30 30, g32p_row21_traceSegment_095_0486_0030, g32p_row21_traceSegment_095_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 546 15 15, g32p_row21_traceSegment_095_0546_0015, g32p_row21_traceSegment_095_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 576 15 16, g32p_row21_traceSegment_095_0576_0015, g32p_row21_traceSegment_095_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 546 30 31, g32p_row21_traceSegment_095_0546_0030, g32p_row21_traceSegment_095_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_095 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 486 60 61, g32p_row21_traceSegment_095_0486_0060, g32p_row21_traceSegment_095_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 607 15 15, g32p_row21_traceSegment_095_0607_0015, g32p_row21_traceSegment_095_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 637 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 652 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 637 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 637 15 16, g32p_row21_traceSegment_095_0637_0015, g32p_row21_traceSegment_095_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 607 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 607 30 31, g32p_row21_traceSegment_095_0607_0030, g32p_row21_traceSegment_095_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 668 15 15, g32p_row21_traceSegment_095_0668_0015, g32p_row21_traceSegment_095_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 713 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 698 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 698 15 16, g32p_row21_traceSegment_095_0698_0015, g32p_row21_traceSegment_095_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 668 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 668 30 31, g32p_row21_traceSegment_095_0668_0030, g32p_row21_traceSegment_095_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_095 607 122 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 607 61 61, g32p_row21_traceSegment_095_0607_0061, g32p_row21_traceSegment_095_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_095 486 243 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 486 121 122, g32p_row21_traceSegment_095_0486_0121, g32p_row21_traceSegment_095_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 729 15 15, g32p_row21_traceSegment_095_0729_0015, g32p_row21_traceSegment_095_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 759 15 15, g32p_row21_traceSegment_095_0759_0015, g32p_row21_traceSegment_095_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_095 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 729 30 30, g32p_row21_traceSegment_095_0729_0030, g32p_row21_traceSegment_095_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 789 15 15, g32p_row21_traceSegment_095_0789_0015, g32p_row21_traceSegment_095_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 819 15 16, g32p_row21_traceSegment_095_0819_0015, g32p_row21_traceSegment_095_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 789 30 31, g32p_row21_traceSegment_095_0789_0030, g32p_row21_traceSegment_095_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_095 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 729 60 61, g32p_row21_traceSegment_095_0729_0060, g32p_row21_traceSegment_095_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 850 15 15, g32p_row21_traceSegment_095_0850_0015, g32p_row21_traceSegment_095_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 880 15 16, g32p_row21_traceSegment_095_0880_0015, g32p_row21_traceSegment_095_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 850 30 31, g32p_row21_traceSegment_095_0850_0030, g32p_row21_traceSegment_095_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_095 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 911 15 15, g32p_row21_traceSegment_095_0911_0015, g32p_row21_traceSegment_095_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_095 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_095 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_095_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_095 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 941 15 16, g32p_row21_traceSegment_095_0941_0015, g32p_row21_traceSegment_095_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_095 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 911 30 31, g32p_row21_traceSegment_095_0911_0030, g32p_row21_traceSegment_095_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_095 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 850 61 61, g32p_row21_traceSegment_095_0850_0061, g32p_row21_traceSegment_095_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_095 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 729 121 122, g32p_row21_traceSegment_095_0729_0121, g32p_row21_traceSegment_095_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_095 486 486 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 486 243 243, g32p_row21_traceSegment_095_0486_0243, g32p_row21_traceSegment_095_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_095_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_095 0 972 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_095 0 486 486, g32p_row21_traceSegment_095_0000_0486, g32p_row21_traceSegment_095_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 95 = [1, 0, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_095_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_096_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 0 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 0 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 0 15 15, g32p_row21_traceSegment_096_0000_0015, g32p_row21_traceSegment_096_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 30 15 15, g32p_row21_traceSegment_096_0030_0015, g32p_row21_traceSegment_096_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_096 0 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 0 30 30, g32p_row21_traceSegment_096_0000_0030, g32p_row21_traceSegment_096_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 60 15 15, g32p_row21_traceSegment_096_0060_0015, g32p_row21_traceSegment_096_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 90 15 16, g32p_row21_traceSegment_096_0090_0015, g32p_row21_traceSegment_096_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 60 30 31, g32p_row21_traceSegment_096_0060_0030, g32p_row21_traceSegment_096_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_096 0 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 0 60 61, g32p_row21_traceSegment_096_0000_0060, g32p_row21_traceSegment_096_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 121 15 15, g32p_row21_traceSegment_096_0121_0015, g32p_row21_traceSegment_096_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 151 15 16, g32p_row21_traceSegment_096_0151_0015, g32p_row21_traceSegment_096_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 121 30 31, g32p_row21_traceSegment_096_0121_0030, g32p_row21_traceSegment_096_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 182 15 15, g32p_row21_traceSegment_096_0182_0015, g32p_row21_traceSegment_096_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 212 15 16, g32p_row21_traceSegment_096_0212_0015, g32p_row21_traceSegment_096_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 182 30 31, g32p_row21_traceSegment_096_0182_0030, g32p_row21_traceSegment_096_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_096 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 121 61 61, g32p_row21_traceSegment_096_0121_0061, g32p_row21_traceSegment_096_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_096 0 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 0 121 122, g32p_row21_traceSegment_096_0000_0121, g32p_row21_traceSegment_096_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 243 15 15, g32p_row21_traceSegment_096_0243_0015, g32p_row21_traceSegment_096_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 273 15 15, g32p_row21_traceSegment_096_0273_0015, g32p_row21_traceSegment_096_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_096 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 243 30 30, g32p_row21_traceSegment_096_0243_0030, g32p_row21_traceSegment_096_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 303 15 15, g32p_row21_traceSegment_096_0303_0015, g32p_row21_traceSegment_096_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 333 15 16, g32p_row21_traceSegment_096_0333_0015, g32p_row21_traceSegment_096_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 303 30 31, g32p_row21_traceSegment_096_0303_0030, g32p_row21_traceSegment_096_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_096 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 243 60 61, g32p_row21_traceSegment_096_0243_0060, g32p_row21_traceSegment_096_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 364 15 15, g32p_row21_traceSegment_096_0364_0015, g32p_row21_traceSegment_096_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 394 15 16, g32p_row21_traceSegment_096_0394_0015, g32p_row21_traceSegment_096_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 364 30 31, g32p_row21_traceSegment_096_0364_0030, g32p_row21_traceSegment_096_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 425 15 15, g32p_row21_traceSegment_096_0425_0015, g32p_row21_traceSegment_096_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 455 15 16, g32p_row21_traceSegment_096_0455_0015, g32p_row21_traceSegment_096_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 425 30 31, g32p_row21_traceSegment_096_0425_0030, g32p_row21_traceSegment_096_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_096 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 364 61 61, g32p_row21_traceSegment_096_0364_0061, g32p_row21_traceSegment_096_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_096 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 243 121 122, g32p_row21_traceSegment_096_0243_0121, g32p_row21_traceSegment_096_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_096 0 486 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 0 243 243, g32p_row21_traceSegment_096_0000_0243, g32p_row21_traceSegment_096_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 486 15 15, g32p_row21_traceSegment_096_0486_0015, g32p_row21_traceSegment_096_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 516 15 15, g32p_row21_traceSegment_096_0516_0015, g32p_row21_traceSegment_096_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_096 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 486 30 30, g32p_row21_traceSegment_096_0486_0030, g32p_row21_traceSegment_096_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 546 15 15, g32p_row21_traceSegment_096_0546_0015, g32p_row21_traceSegment_096_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 576 15 16, g32p_row21_traceSegment_096_0576_0015, g32p_row21_traceSegment_096_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 546 30 31, g32p_row21_traceSegment_096_0546_0030, g32p_row21_traceSegment_096_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_096 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 486 60 61, g32p_row21_traceSegment_096_0486_0060, g32p_row21_traceSegment_096_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 607 15 15, g32p_row21_traceSegment_096_0607_0015, g32p_row21_traceSegment_096_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 637 15 16, g32p_row21_traceSegment_096_0637_0015, g32p_row21_traceSegment_096_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 607 30 31, g32p_row21_traceSegment_096_0607_0030, g32p_row21_traceSegment_096_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 668 15 15, g32p_row21_traceSegment_096_0668_0015, g32p_row21_traceSegment_096_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 698 15 16, g32p_row21_traceSegment_096_0698_0015, g32p_row21_traceSegment_096_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 668 30 31, g32p_row21_traceSegment_096_0668_0030, g32p_row21_traceSegment_096_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_096 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 607 61 61, g32p_row21_traceSegment_096_0607_0061, g32p_row21_traceSegment_096_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_096 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 486 121 122, g32p_row21_traceSegment_096_0486_0121, g32p_row21_traceSegment_096_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 729 15 15, g32p_row21_traceSegment_096_0729_0015, g32p_row21_traceSegment_096_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 759 15 15, g32p_row21_traceSegment_096_0759_0015, g32p_row21_traceSegment_096_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_096 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 729 30 30, g32p_row21_traceSegment_096_0729_0030, g32p_row21_traceSegment_096_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 789 15 15, g32p_row21_traceSegment_096_0789_0015, g32p_row21_traceSegment_096_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 819 15 16, g32p_row21_traceSegment_096_0819_0015, g32p_row21_traceSegment_096_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 789 30 31, g32p_row21_traceSegment_096_0789_0030, g32p_row21_traceSegment_096_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_096 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 729 60 61, g32p_row21_traceSegment_096_0729_0060, g32p_row21_traceSegment_096_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 850 15 15, g32p_row21_traceSegment_096_0850_0015, g32p_row21_traceSegment_096_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 880 15 16, g32p_row21_traceSegment_096_0880_0015, g32p_row21_traceSegment_096_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 850 30 31, g32p_row21_traceSegment_096_0850_0030, g32p_row21_traceSegment_096_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_096 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 911 15 15, g32p_row21_traceSegment_096_0911_0015, g32p_row21_traceSegment_096_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_096 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_096 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_096_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_096 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 941 15 16, g32p_row21_traceSegment_096_0941_0015, g32p_row21_traceSegment_096_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_096 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 911 30 31, g32p_row21_traceSegment_096_0911_0030, g32p_row21_traceSegment_096_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_096 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 850 61 61, g32p_row21_traceSegment_096_0850_0061, g32p_row21_traceSegment_096_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_096 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 729 121 122, g32p_row21_traceSegment_096_0729_0121, g32p_row21_traceSegment_096_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_096 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 486 243 243, g32p_row21_traceSegment_096_0486_0243, g32p_row21_traceSegment_096_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_096_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_096 0 972 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_096 0 486 486, g32p_row21_traceSegment_096_0000_0486, g32p_row21_traceSegment_096_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 96 = [0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_096_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row21_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 87) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 87) (g32p_literalTraceValue 20 87)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_087]
  decide +kernel

theorem g32p_row21_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 88) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 88) (g32p_literalTraceValue 20 88)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_088]
  decide +kernel

theorem g32p_row21_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 89) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 89) (g32p_literalTraceValue 20 89)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_089]
  decide +kernel

theorem g32p_row21_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 91) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 91) (g32p_literalTraceValue 20 91)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_091]
  decide +kernel

theorem g32p_row21_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 92) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 92) (g32p_literalTraceValue 20 92)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_092]
  decide +kernel

theorem g32p_row21_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 93) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 93) (g32p_literalTraceValue 20 93)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_093]
  decide +kernel

theorem g32p_row21_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 95) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 95) (g32p_literalTraceValue 20 95)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row21_traceCoefficients_095]
  decide +kernel

theorem g32p_row21_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 96) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 96) (g32p_literalTraceValue 20 96)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_096]
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

private def g32p_row21_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_097_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 15 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 0 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 0 15 15, g32p_row21_traceSegment_097_0000_0015, g32p_row21_traceSegment_097_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 30 15 15, g32p_row21_traceSegment_097_0030_0015, g32p_row21_traceSegment_097_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_097 0 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 0 30 30, g32p_row21_traceSegment_097_0000_0030, g32p_row21_traceSegment_097_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 60 15 15, g32p_row21_traceSegment_097_0060_0015, g32p_row21_traceSegment_097_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 90 15 16, g32p_row21_traceSegment_097_0090_0015, g32p_row21_traceSegment_097_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 60 30 31, g32p_row21_traceSegment_097_0060_0030, g32p_row21_traceSegment_097_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_097 0 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 0 60 61, g32p_row21_traceSegment_097_0000_0060, g32p_row21_traceSegment_097_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 121 15 15, g32p_row21_traceSegment_097_0121_0015, g32p_row21_traceSegment_097_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 151 15 16, g32p_row21_traceSegment_097_0151_0015, g32p_row21_traceSegment_097_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 121 30 31, g32p_row21_traceSegment_097_0121_0030, g32p_row21_traceSegment_097_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 182 15 15, g32p_row21_traceSegment_097_0182_0015, g32p_row21_traceSegment_097_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 212 15 16, g32p_row21_traceSegment_097_0212_0015, g32p_row21_traceSegment_097_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 182 30 31, g32p_row21_traceSegment_097_0182_0030, g32p_row21_traceSegment_097_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_097 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 121 61 61, g32p_row21_traceSegment_097_0121_0061, g32p_row21_traceSegment_097_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_097 0 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 0 121 122, g32p_row21_traceSegment_097_0000_0121, g32p_row21_traceSegment_097_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 243 15 15, g32p_row21_traceSegment_097_0243_0015, g32p_row21_traceSegment_097_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 273 15 15, g32p_row21_traceSegment_097_0273_0015, g32p_row21_traceSegment_097_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_097 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 243 30 30, g32p_row21_traceSegment_097_0243_0030, g32p_row21_traceSegment_097_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 303 15 15, g32p_row21_traceSegment_097_0303_0015, g32p_row21_traceSegment_097_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 333 15 16, g32p_row21_traceSegment_097_0333_0015, g32p_row21_traceSegment_097_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 303 30 31, g32p_row21_traceSegment_097_0303_0030, g32p_row21_traceSegment_097_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_097 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 243 60 61, g32p_row21_traceSegment_097_0243_0060, g32p_row21_traceSegment_097_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 364 15 15, g32p_row21_traceSegment_097_0364_0015, g32p_row21_traceSegment_097_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 394 15 16, g32p_row21_traceSegment_097_0394_0015, g32p_row21_traceSegment_097_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 364 30 31, g32p_row21_traceSegment_097_0364_0030, g32p_row21_traceSegment_097_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 425 15 15, g32p_row21_traceSegment_097_0425_0015, g32p_row21_traceSegment_097_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 455 15 16, g32p_row21_traceSegment_097_0455_0015, g32p_row21_traceSegment_097_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 425 30 31, g32p_row21_traceSegment_097_0425_0030, g32p_row21_traceSegment_097_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_097 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 364 61 61, g32p_row21_traceSegment_097_0364_0061, g32p_row21_traceSegment_097_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_097 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 243 121 122, g32p_row21_traceSegment_097_0243_0121, g32p_row21_traceSegment_097_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_097 0 486 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 0 243 243, g32p_row21_traceSegment_097_0000_0243, g32p_row21_traceSegment_097_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 486 15 15, g32p_row21_traceSegment_097_0486_0015, g32p_row21_traceSegment_097_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 516 15 15, g32p_row21_traceSegment_097_0516_0015, g32p_row21_traceSegment_097_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_097 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 486 30 30, g32p_row21_traceSegment_097_0486_0030, g32p_row21_traceSegment_097_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 546 15 15, g32p_row21_traceSegment_097_0546_0015, g32p_row21_traceSegment_097_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 576 15 16, g32p_row21_traceSegment_097_0576_0015, g32p_row21_traceSegment_097_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 546 30 31, g32p_row21_traceSegment_097_0546_0030, g32p_row21_traceSegment_097_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_097 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 486 60 61, g32p_row21_traceSegment_097_0486_0060, g32p_row21_traceSegment_097_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 607 15 15, g32p_row21_traceSegment_097_0607_0015, g32p_row21_traceSegment_097_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 637 15 16, g32p_row21_traceSegment_097_0637_0015, g32p_row21_traceSegment_097_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 607 30 31, g32p_row21_traceSegment_097_0607_0030, g32p_row21_traceSegment_097_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 668 15 15, g32p_row21_traceSegment_097_0668_0015, g32p_row21_traceSegment_097_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 698 15 16, g32p_row21_traceSegment_097_0698_0015, g32p_row21_traceSegment_097_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 668 30 31, g32p_row21_traceSegment_097_0668_0030, g32p_row21_traceSegment_097_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_097 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 607 61 61, g32p_row21_traceSegment_097_0607_0061, g32p_row21_traceSegment_097_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_097 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 486 121 122, g32p_row21_traceSegment_097_0486_0121, g32p_row21_traceSegment_097_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 729 15 15, g32p_row21_traceSegment_097_0729_0015, g32p_row21_traceSegment_097_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 759 15 15, g32p_row21_traceSegment_097_0759_0015, g32p_row21_traceSegment_097_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_097 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 729 30 30, g32p_row21_traceSegment_097_0729_0030, g32p_row21_traceSegment_097_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 789 15 15, g32p_row21_traceSegment_097_0789_0015, g32p_row21_traceSegment_097_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 819 15 16, g32p_row21_traceSegment_097_0819_0015, g32p_row21_traceSegment_097_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 789 30 31, g32p_row21_traceSegment_097_0789_0030, g32p_row21_traceSegment_097_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_097 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 729 60 61, g32p_row21_traceSegment_097_0729_0060, g32p_row21_traceSegment_097_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 850 15 15, g32p_row21_traceSegment_097_0850_0015, g32p_row21_traceSegment_097_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 880 15 16, g32p_row21_traceSegment_097_0880_0015, g32p_row21_traceSegment_097_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 850 30 31, g32p_row21_traceSegment_097_0850_0030, g32p_row21_traceSegment_097_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_097 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 911 15 15, g32p_row21_traceSegment_097_0911_0015, g32p_row21_traceSegment_097_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_097 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_097 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_097_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_097 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 941 15 16, g32p_row21_traceSegment_097_0941_0015, g32p_row21_traceSegment_097_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_097 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 911 30 31, g32p_row21_traceSegment_097_0911_0030, g32p_row21_traceSegment_097_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_097 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 850 61 61, g32p_row21_traceSegment_097_0850_0061, g32p_row21_traceSegment_097_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_097 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 729 121 122, g32p_row21_traceSegment_097_0729_0121, g32p_row21_traceSegment_097_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_097 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 486 243 243, g32p_row21_traceSegment_097_0486_0243, g32p_row21_traceSegment_097_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_097_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_097 0 972 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_097 0 486 486, g32p_row21_traceSegment_097_0000_0486, g32p_row21_traceSegment_097_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 97 = [0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_097_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_098 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 98 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_098_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 15 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 0 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 0 15 15, g32p_row21_traceSegment_098_0000_0015, g32p_row21_traceSegment_098_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 30 15 15, g32p_row21_traceSegment_098_0030_0015, g32p_row21_traceSegment_098_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_098 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 0 30 30, g32p_row21_traceSegment_098_0000_0030, g32p_row21_traceSegment_098_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 60 15 15, g32p_row21_traceSegment_098_0060_0015, g32p_row21_traceSegment_098_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 90 15 16, g32p_row21_traceSegment_098_0090_0015, g32p_row21_traceSegment_098_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 60 30 31, g32p_row21_traceSegment_098_0060_0030, g32p_row21_traceSegment_098_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_098 0 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 0 60 61, g32p_row21_traceSegment_098_0000_0060, g32p_row21_traceSegment_098_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 121 15 15, g32p_row21_traceSegment_098_0121_0015, g32p_row21_traceSegment_098_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 151 15 16, g32p_row21_traceSegment_098_0151_0015, g32p_row21_traceSegment_098_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 121 30 31, g32p_row21_traceSegment_098_0121_0030, g32p_row21_traceSegment_098_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 182 15 15, g32p_row21_traceSegment_098_0182_0015, g32p_row21_traceSegment_098_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 212 15 16, g32p_row21_traceSegment_098_0212_0015, g32p_row21_traceSegment_098_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 182 30 31, g32p_row21_traceSegment_098_0182_0030, g32p_row21_traceSegment_098_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_098 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 121 61 61, g32p_row21_traceSegment_098_0121_0061, g32p_row21_traceSegment_098_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_098 0 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 0 121 122, g32p_row21_traceSegment_098_0000_0121, g32p_row21_traceSegment_098_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 243 15 15, g32p_row21_traceSegment_098_0243_0015, g32p_row21_traceSegment_098_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 273 15 15, g32p_row21_traceSegment_098_0273_0015, g32p_row21_traceSegment_098_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_098 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 243 30 30, g32p_row21_traceSegment_098_0243_0030, g32p_row21_traceSegment_098_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 303 15 15, g32p_row21_traceSegment_098_0303_0015, g32p_row21_traceSegment_098_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 333 15 16, g32p_row21_traceSegment_098_0333_0015, g32p_row21_traceSegment_098_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 303 30 31, g32p_row21_traceSegment_098_0303_0030, g32p_row21_traceSegment_098_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_098 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 243 60 61, g32p_row21_traceSegment_098_0243_0060, g32p_row21_traceSegment_098_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 364 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 379 15 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 364 30 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 364 15 15, g32p_row21_traceSegment_098_0364_0015, g32p_row21_traceSegment_098_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 394 15 16, g32p_row21_traceSegment_098_0394_0015, g32p_row21_traceSegment_098_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 364 61 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 364 30 31, g32p_row21_traceSegment_098_0364_0030, g32p_row21_traceSegment_098_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 425 15 15, g32p_row21_traceSegment_098_0425_0015, g32p_row21_traceSegment_098_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 455 15 16, g32p_row21_traceSegment_098_0455_0015, g32p_row21_traceSegment_098_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 425 30 31, g32p_row21_traceSegment_098_0425_0030, g32p_row21_traceSegment_098_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_098 364 122 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 364 61 61, g32p_row21_traceSegment_098_0364_0061, g32p_row21_traceSegment_098_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_098 243 243 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 243 121 122, g32p_row21_traceSegment_098_0243_0121, g32p_row21_traceSegment_098_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_098 0 486 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 0 243 243, g32p_row21_traceSegment_098_0000_0243, g32p_row21_traceSegment_098_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 486 15 15, g32p_row21_traceSegment_098_0486_0015, g32p_row21_traceSegment_098_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 516 15 15, g32p_row21_traceSegment_098_0516_0015, g32p_row21_traceSegment_098_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_098 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 486 30 30, g32p_row21_traceSegment_098_0486_0030, g32p_row21_traceSegment_098_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 546 15 15, g32p_row21_traceSegment_098_0546_0015, g32p_row21_traceSegment_098_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 576 15 16, g32p_row21_traceSegment_098_0576_0015, g32p_row21_traceSegment_098_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 546 30 31, g32p_row21_traceSegment_098_0546_0030, g32p_row21_traceSegment_098_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_098 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 486 60 61, g32p_row21_traceSegment_098_0486_0060, g32p_row21_traceSegment_098_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 607 15 15, g32p_row21_traceSegment_098_0607_0015, g32p_row21_traceSegment_098_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 637 15 16, g32p_row21_traceSegment_098_0637_0015, g32p_row21_traceSegment_098_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 607 30 31, g32p_row21_traceSegment_098_0607_0030, g32p_row21_traceSegment_098_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 668 15 15, g32p_row21_traceSegment_098_0668_0015, g32p_row21_traceSegment_098_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 698 15 16, g32p_row21_traceSegment_098_0698_0015, g32p_row21_traceSegment_098_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 668 30 31, g32p_row21_traceSegment_098_0668_0030, g32p_row21_traceSegment_098_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_098 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 607 61 61, g32p_row21_traceSegment_098_0607_0061, g32p_row21_traceSegment_098_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_098 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 486 121 122, g32p_row21_traceSegment_098_0486_0121, g32p_row21_traceSegment_098_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 729 15 15, g32p_row21_traceSegment_098_0729_0015, g32p_row21_traceSegment_098_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 759 15 15, g32p_row21_traceSegment_098_0759_0015, g32p_row21_traceSegment_098_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_098 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 729 30 30, g32p_row21_traceSegment_098_0729_0030, g32p_row21_traceSegment_098_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 789 15 15, g32p_row21_traceSegment_098_0789_0015, g32p_row21_traceSegment_098_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 819 15 16, g32p_row21_traceSegment_098_0819_0015, g32p_row21_traceSegment_098_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 789 30 31, g32p_row21_traceSegment_098_0789_0030, g32p_row21_traceSegment_098_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_098 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 729 60 61, g32p_row21_traceSegment_098_0729_0060, g32p_row21_traceSegment_098_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 850 15 15, g32p_row21_traceSegment_098_0850_0015, g32p_row21_traceSegment_098_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 880 15 16, g32p_row21_traceSegment_098_0880_0015, g32p_row21_traceSegment_098_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 850 30 31, g32p_row21_traceSegment_098_0850_0030, g32p_row21_traceSegment_098_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_098 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 911 15 15, g32p_row21_traceSegment_098_0911_0015, g32p_row21_traceSegment_098_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_098 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_098 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_098_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_098 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 941 15 16, g32p_row21_traceSegment_098_0941_0015, g32p_row21_traceSegment_098_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_098 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 911 30 31, g32p_row21_traceSegment_098_0911_0030, g32p_row21_traceSegment_098_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_098 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 850 61 61, g32p_row21_traceSegment_098_0850_0061, g32p_row21_traceSegment_098_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_098 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 729 121 122, g32p_row21_traceSegment_098_0729_0121, g32p_row21_traceSegment_098_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_098 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 486 243 243, g32p_row21_traceSegment_098_0486_0243, g32p_row21_traceSegment_098_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_098_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_098 0 972 = [0, 1, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_098 0 486 486, g32p_row21_traceSegment_098_0000_0486, g32p_row21_traceSegment_098_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 98 = [0, 1, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_098_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_099_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 0 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 0 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 0 15 15, g32p_row21_traceSegment_099_0000_0015, g32p_row21_traceSegment_099_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 30 15 15, g32p_row21_traceSegment_099_0030_0015, g32p_row21_traceSegment_099_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_099 0 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 0 30 30, g32p_row21_traceSegment_099_0000_0030, g32p_row21_traceSegment_099_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 60 15 15, g32p_row21_traceSegment_099_0060_0015, g32p_row21_traceSegment_099_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 90 15 16, g32p_row21_traceSegment_099_0090_0015, g32p_row21_traceSegment_099_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 60 30 31, g32p_row21_traceSegment_099_0060_0030, g32p_row21_traceSegment_099_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_099 0 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 0 60 61, g32p_row21_traceSegment_099_0000_0060, g32p_row21_traceSegment_099_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 121 15 15, g32p_row21_traceSegment_099_0121_0015, g32p_row21_traceSegment_099_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 151 15 16, g32p_row21_traceSegment_099_0151_0015, g32p_row21_traceSegment_099_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 121 30 31, g32p_row21_traceSegment_099_0121_0030, g32p_row21_traceSegment_099_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 182 15 15, g32p_row21_traceSegment_099_0182_0015, g32p_row21_traceSegment_099_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 212 15 16, g32p_row21_traceSegment_099_0212_0015, g32p_row21_traceSegment_099_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 182 30 31, g32p_row21_traceSegment_099_0182_0030, g32p_row21_traceSegment_099_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_099 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 121 61 61, g32p_row21_traceSegment_099_0121_0061, g32p_row21_traceSegment_099_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_099 0 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 0 121 122, g32p_row21_traceSegment_099_0000_0121, g32p_row21_traceSegment_099_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 243 15 15, g32p_row21_traceSegment_099_0243_0015, g32p_row21_traceSegment_099_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 273 15 15, g32p_row21_traceSegment_099_0273_0015, g32p_row21_traceSegment_099_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_099 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 243 30 30, g32p_row21_traceSegment_099_0243_0030, g32p_row21_traceSegment_099_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 303 15 15, g32p_row21_traceSegment_099_0303_0015, g32p_row21_traceSegment_099_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 333 15 16, g32p_row21_traceSegment_099_0333_0015, g32p_row21_traceSegment_099_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 303 30 31, g32p_row21_traceSegment_099_0303_0030, g32p_row21_traceSegment_099_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_099 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 243 60 61, g32p_row21_traceSegment_099_0243_0060, g32p_row21_traceSegment_099_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 364 15 15, g32p_row21_traceSegment_099_0364_0015, g32p_row21_traceSegment_099_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 394 15 16, g32p_row21_traceSegment_099_0394_0015, g32p_row21_traceSegment_099_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 364 30 31, g32p_row21_traceSegment_099_0364_0030, g32p_row21_traceSegment_099_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 425 15 15, g32p_row21_traceSegment_099_0425_0015, g32p_row21_traceSegment_099_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 455 15 16, g32p_row21_traceSegment_099_0455_0015, g32p_row21_traceSegment_099_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 425 30 31, g32p_row21_traceSegment_099_0425_0030, g32p_row21_traceSegment_099_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_099 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 364 61 61, g32p_row21_traceSegment_099_0364_0061, g32p_row21_traceSegment_099_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_099 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 243 121 122, g32p_row21_traceSegment_099_0243_0121, g32p_row21_traceSegment_099_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_099 0 486 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 0 243 243, g32p_row21_traceSegment_099_0000_0243, g32p_row21_traceSegment_099_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 486 15 15, g32p_row21_traceSegment_099_0486_0015, g32p_row21_traceSegment_099_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 516 15 15, g32p_row21_traceSegment_099_0516_0015, g32p_row21_traceSegment_099_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_099 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 486 30 30, g32p_row21_traceSegment_099_0486_0030, g32p_row21_traceSegment_099_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 546 15 15, g32p_row21_traceSegment_099_0546_0015, g32p_row21_traceSegment_099_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 576 15 16, g32p_row21_traceSegment_099_0576_0015, g32p_row21_traceSegment_099_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 546 30 31, g32p_row21_traceSegment_099_0546_0030, g32p_row21_traceSegment_099_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_099 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 486 60 61, g32p_row21_traceSegment_099_0486_0060, g32p_row21_traceSegment_099_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 607 15 15, g32p_row21_traceSegment_099_0607_0015, g32p_row21_traceSegment_099_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 637 15 16, g32p_row21_traceSegment_099_0637_0015, g32p_row21_traceSegment_099_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 607 30 31, g32p_row21_traceSegment_099_0607_0030, g32p_row21_traceSegment_099_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 668 15 15, g32p_row21_traceSegment_099_0668_0015, g32p_row21_traceSegment_099_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 698 15 16, g32p_row21_traceSegment_099_0698_0015, g32p_row21_traceSegment_099_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 668 30 31, g32p_row21_traceSegment_099_0668_0030, g32p_row21_traceSegment_099_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_099 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 607 61 61, g32p_row21_traceSegment_099_0607_0061, g32p_row21_traceSegment_099_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_099 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 486 121 122, g32p_row21_traceSegment_099_0486_0121, g32p_row21_traceSegment_099_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 729 15 15, g32p_row21_traceSegment_099_0729_0015, g32p_row21_traceSegment_099_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 759 15 15, g32p_row21_traceSegment_099_0759_0015, g32p_row21_traceSegment_099_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_099 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 729 30 30, g32p_row21_traceSegment_099_0729_0030, g32p_row21_traceSegment_099_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 789 15 15, g32p_row21_traceSegment_099_0789_0015, g32p_row21_traceSegment_099_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 819 15 16, g32p_row21_traceSegment_099_0819_0015, g32p_row21_traceSegment_099_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 789 30 31, g32p_row21_traceSegment_099_0789_0030, g32p_row21_traceSegment_099_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_099 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 729 60 61, g32p_row21_traceSegment_099_0729_0060, g32p_row21_traceSegment_099_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 850 15 15, g32p_row21_traceSegment_099_0850_0015, g32p_row21_traceSegment_099_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 880 15 16, g32p_row21_traceSegment_099_0880_0015, g32p_row21_traceSegment_099_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 850 30 31, g32p_row21_traceSegment_099_0850_0030, g32p_row21_traceSegment_099_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_099 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 911 15 15, g32p_row21_traceSegment_099_0911_0015, g32p_row21_traceSegment_099_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_099 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_099 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_099_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_099 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 941 15 16, g32p_row21_traceSegment_099_0941_0015, g32p_row21_traceSegment_099_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_099 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 911 30 31, g32p_row21_traceSegment_099_0911_0030, g32p_row21_traceSegment_099_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_099 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 850 61 61, g32p_row21_traceSegment_099_0850_0061, g32p_row21_traceSegment_099_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_099 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 729 121 122, g32p_row21_traceSegment_099_0729_0121, g32p_row21_traceSegment_099_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_099 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 486 243 243, g32p_row21_traceSegment_099_0486_0243, g32p_row21_traceSegment_099_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_099_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_099 0 972 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_099 0 486 486, g32p_row21_traceSegment_099_0000_0486, g32p_row21_traceSegment_099_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_099_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_100 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 100 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_100_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 0 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 0 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 0 15 15, g32p_row21_traceSegment_100_0000_0015, g32p_row21_traceSegment_100_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 30 15 15, g32p_row21_traceSegment_100_0030_0015, g32p_row21_traceSegment_100_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_100 0 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 0 30 30, g32p_row21_traceSegment_100_0000_0030, g32p_row21_traceSegment_100_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 60 15 15, g32p_row21_traceSegment_100_0060_0015, g32p_row21_traceSegment_100_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 90 15 16, g32p_row21_traceSegment_100_0090_0015, g32p_row21_traceSegment_100_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 60 30 31, g32p_row21_traceSegment_100_0060_0030, g32p_row21_traceSegment_100_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_100 0 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 0 60 61, g32p_row21_traceSegment_100_0000_0060, g32p_row21_traceSegment_100_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 121 15 15, g32p_row21_traceSegment_100_0121_0015, g32p_row21_traceSegment_100_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 151 15 16, g32p_row21_traceSegment_100_0151_0015, g32p_row21_traceSegment_100_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 121 30 31, g32p_row21_traceSegment_100_0121_0030, g32p_row21_traceSegment_100_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 182 15 15, g32p_row21_traceSegment_100_0182_0015, g32p_row21_traceSegment_100_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 227 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 212 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 212 15 16, g32p_row21_traceSegment_100_0212_0015, g32p_row21_traceSegment_100_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 182 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 182 30 31, g32p_row21_traceSegment_100_0182_0030, g32p_row21_traceSegment_100_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_100 121 122 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 121 61 61, g32p_row21_traceSegment_100_0121_0061, g32p_row21_traceSegment_100_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_100 0 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 0 121 122, g32p_row21_traceSegment_100_0000_0121, g32p_row21_traceSegment_100_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 243 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 243 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 243 15 15, g32p_row21_traceSegment_100_0243_0015, g32p_row21_traceSegment_100_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 273 15 15, g32p_row21_traceSegment_100_0273_0015, g32p_row21_traceSegment_100_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_100 243 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 243 30 30, g32p_row21_traceSegment_100_0243_0030, g32p_row21_traceSegment_100_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 303 15 15, g32p_row21_traceSegment_100_0303_0015, g32p_row21_traceSegment_100_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 333 15 16, g32p_row21_traceSegment_100_0333_0015, g32p_row21_traceSegment_100_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 303 30 31, g32p_row21_traceSegment_100_0303_0030, g32p_row21_traceSegment_100_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_100 243 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 243 60 61, g32p_row21_traceSegment_100_0243_0060, g32p_row21_traceSegment_100_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 364 15 15, g32p_row21_traceSegment_100_0364_0015, g32p_row21_traceSegment_100_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 394 15 16, g32p_row21_traceSegment_100_0394_0015, g32p_row21_traceSegment_100_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 364 30 31, g32p_row21_traceSegment_100_0364_0030, g32p_row21_traceSegment_100_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 425 15 15, g32p_row21_traceSegment_100_0425_0015, g32p_row21_traceSegment_100_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 455 15 16, g32p_row21_traceSegment_100_0455_0015, g32p_row21_traceSegment_100_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 425 30 31, g32p_row21_traceSegment_100_0425_0030, g32p_row21_traceSegment_100_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_100 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 364 61 61, g32p_row21_traceSegment_100_0364_0061, g32p_row21_traceSegment_100_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_100 243 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 243 121 122, g32p_row21_traceSegment_100_0243_0121, g32p_row21_traceSegment_100_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_100 0 486 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 0 243 243, g32p_row21_traceSegment_100_0000_0243, g32p_row21_traceSegment_100_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 486 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 486 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 486 15 15, g32p_row21_traceSegment_100_0486_0015, g32p_row21_traceSegment_100_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 516 15 15, g32p_row21_traceSegment_100_0516_0015, g32p_row21_traceSegment_100_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_100 486 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 486 30 30, g32p_row21_traceSegment_100_0486_0030, g32p_row21_traceSegment_100_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 546 15 15, g32p_row21_traceSegment_100_0546_0015, g32p_row21_traceSegment_100_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 576 15 16, g32p_row21_traceSegment_100_0576_0015, g32p_row21_traceSegment_100_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 546 30 31, g32p_row21_traceSegment_100_0546_0030, g32p_row21_traceSegment_100_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_100 486 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 486 60 61, g32p_row21_traceSegment_100_0486_0060, g32p_row21_traceSegment_100_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 607 15 15, g32p_row21_traceSegment_100_0607_0015, g32p_row21_traceSegment_100_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 637 15 16, g32p_row21_traceSegment_100_0637_0015, g32p_row21_traceSegment_100_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 607 30 31, g32p_row21_traceSegment_100_0607_0030, g32p_row21_traceSegment_100_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 668 15 15, g32p_row21_traceSegment_100_0668_0015, g32p_row21_traceSegment_100_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 698 15 16, g32p_row21_traceSegment_100_0698_0015, g32p_row21_traceSegment_100_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 668 30 31, g32p_row21_traceSegment_100_0668_0030, g32p_row21_traceSegment_100_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_100 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 607 61 61, g32p_row21_traceSegment_100_0607_0061, g32p_row21_traceSegment_100_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_100 486 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 486 121 122, g32p_row21_traceSegment_100_0486_0121, g32p_row21_traceSegment_100_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 729 15 15, g32p_row21_traceSegment_100_0729_0015, g32p_row21_traceSegment_100_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 759 15 15, g32p_row21_traceSegment_100_0759_0015, g32p_row21_traceSegment_100_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_100 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 729 30 30, g32p_row21_traceSegment_100_0729_0030, g32p_row21_traceSegment_100_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 789 15 15, g32p_row21_traceSegment_100_0789_0015, g32p_row21_traceSegment_100_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 819 15 16, g32p_row21_traceSegment_100_0819_0015, g32p_row21_traceSegment_100_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 789 30 31, g32p_row21_traceSegment_100_0789_0030, g32p_row21_traceSegment_100_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_100 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 729 60 61, g32p_row21_traceSegment_100_0729_0060, g32p_row21_traceSegment_100_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 850 15 15, g32p_row21_traceSegment_100_0850_0015, g32p_row21_traceSegment_100_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 880 15 16, g32p_row21_traceSegment_100_0880_0015, g32p_row21_traceSegment_100_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 850 30 31, g32p_row21_traceSegment_100_0850_0030, g32p_row21_traceSegment_100_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_100 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 911 15 15, g32p_row21_traceSegment_100_0911_0015, g32p_row21_traceSegment_100_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_100 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_100 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_100_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_100 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 941 15 16, g32p_row21_traceSegment_100_0941_0015, g32p_row21_traceSegment_100_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_100 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 911 30 31, g32p_row21_traceSegment_100_0911_0030, g32p_row21_traceSegment_100_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_100 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 850 61 61, g32p_row21_traceSegment_100_0850_0061, g32p_row21_traceSegment_100_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_100 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 729 121 122, g32p_row21_traceSegment_100_0729_0121, g32p_row21_traceSegment_100_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_100 486 486 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 486 243 243, g32p_row21_traceSegment_100_0486_0243, g32p_row21_traceSegment_100_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_100_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_100 0 972 = [3, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_100 0 486 486, g32p_row21_traceSegment_100_0000_0486, g32p_row21_traceSegment_100_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 100 = [3, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_100_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_101 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 101 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_101_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 0 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 0 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 0 15 15, g32p_row21_traceSegment_101_0000_0015, g32p_row21_traceSegment_101_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 30 15 15, g32p_row21_traceSegment_101_0030_0015, g32p_row21_traceSegment_101_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_101 0 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 0 30 30, g32p_row21_traceSegment_101_0000_0030, g32p_row21_traceSegment_101_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 60 15 15, g32p_row21_traceSegment_101_0060_0015, g32p_row21_traceSegment_101_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 90 15 16, g32p_row21_traceSegment_101_0090_0015, g32p_row21_traceSegment_101_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 60 30 31, g32p_row21_traceSegment_101_0060_0030, g32p_row21_traceSegment_101_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_101 0 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 0 60 61, g32p_row21_traceSegment_101_0000_0060, g32p_row21_traceSegment_101_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 121 15 15, g32p_row21_traceSegment_101_0121_0015, g32p_row21_traceSegment_101_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 151 15 16, g32p_row21_traceSegment_101_0151_0015, g32p_row21_traceSegment_101_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 121 30 31, g32p_row21_traceSegment_101_0121_0030, g32p_row21_traceSegment_101_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 182 15 15, g32p_row21_traceSegment_101_0182_0015, g32p_row21_traceSegment_101_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 212 15 16, g32p_row21_traceSegment_101_0212_0015, g32p_row21_traceSegment_101_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 182 30 31, g32p_row21_traceSegment_101_0182_0030, g32p_row21_traceSegment_101_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_101 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 121 61 61, g32p_row21_traceSegment_101_0121_0061, g32p_row21_traceSegment_101_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_101 0 243 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 0 121 122, g32p_row21_traceSegment_101_0000_0121, g32p_row21_traceSegment_101_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 243 15 15, g32p_row21_traceSegment_101_0243_0015, g32p_row21_traceSegment_101_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 273 15 15, g32p_row21_traceSegment_101_0273_0015, g32p_row21_traceSegment_101_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_101 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 243 30 30, g32p_row21_traceSegment_101_0243_0030, g32p_row21_traceSegment_101_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 303 15 15, g32p_row21_traceSegment_101_0303_0015, g32p_row21_traceSegment_101_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 333 15 16, g32p_row21_traceSegment_101_0333_0015, g32p_row21_traceSegment_101_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 303 30 31, g32p_row21_traceSegment_101_0303_0030, g32p_row21_traceSegment_101_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_101 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 243 60 61, g32p_row21_traceSegment_101_0243_0060, g32p_row21_traceSegment_101_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 364 15 15, g32p_row21_traceSegment_101_0364_0015, g32p_row21_traceSegment_101_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 394 15 16, g32p_row21_traceSegment_101_0394_0015, g32p_row21_traceSegment_101_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 364 30 31, g32p_row21_traceSegment_101_0364_0030, g32p_row21_traceSegment_101_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 425 15 15, g32p_row21_traceSegment_101_0425_0015, g32p_row21_traceSegment_101_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 455 15 16, g32p_row21_traceSegment_101_0455_0015, g32p_row21_traceSegment_101_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 425 30 31, g32p_row21_traceSegment_101_0425_0030, g32p_row21_traceSegment_101_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_101 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 364 61 61, g32p_row21_traceSegment_101_0364_0061, g32p_row21_traceSegment_101_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_101 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 243 121 122, g32p_row21_traceSegment_101_0243_0121, g32p_row21_traceSegment_101_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_101 0 486 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 0 243 243, g32p_row21_traceSegment_101_0000_0243, g32p_row21_traceSegment_101_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 486 15 15, g32p_row21_traceSegment_101_0486_0015, g32p_row21_traceSegment_101_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 516 15 15, g32p_row21_traceSegment_101_0516_0015, g32p_row21_traceSegment_101_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_101 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 486 30 30, g32p_row21_traceSegment_101_0486_0030, g32p_row21_traceSegment_101_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 546 15 15, g32p_row21_traceSegment_101_0546_0015, g32p_row21_traceSegment_101_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 576 15 16, g32p_row21_traceSegment_101_0576_0015, g32p_row21_traceSegment_101_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 546 30 31, g32p_row21_traceSegment_101_0546_0030, g32p_row21_traceSegment_101_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_101 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 486 60 61, g32p_row21_traceSegment_101_0486_0060, g32p_row21_traceSegment_101_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 607 15 15, g32p_row21_traceSegment_101_0607_0015, g32p_row21_traceSegment_101_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 637 15 16, g32p_row21_traceSegment_101_0637_0015, g32p_row21_traceSegment_101_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 607 30 31, g32p_row21_traceSegment_101_0607_0030, g32p_row21_traceSegment_101_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 668 15 15, g32p_row21_traceSegment_101_0668_0015, g32p_row21_traceSegment_101_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 698 15 16, g32p_row21_traceSegment_101_0698_0015, g32p_row21_traceSegment_101_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 668 30 31, g32p_row21_traceSegment_101_0668_0030, g32p_row21_traceSegment_101_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_101 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 607 61 61, g32p_row21_traceSegment_101_0607_0061, g32p_row21_traceSegment_101_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_101 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 486 121 122, g32p_row21_traceSegment_101_0486_0121, g32p_row21_traceSegment_101_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 729 15 15, g32p_row21_traceSegment_101_0729_0015, g32p_row21_traceSegment_101_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 759 15 15, g32p_row21_traceSegment_101_0759_0015, g32p_row21_traceSegment_101_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_101 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 729 30 30, g32p_row21_traceSegment_101_0729_0030, g32p_row21_traceSegment_101_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 789 15 15, g32p_row21_traceSegment_101_0789_0015, g32p_row21_traceSegment_101_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 819 15 16, g32p_row21_traceSegment_101_0819_0015, g32p_row21_traceSegment_101_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 789 30 31, g32p_row21_traceSegment_101_0789_0030, g32p_row21_traceSegment_101_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_101 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 729 60 61, g32p_row21_traceSegment_101_0729_0060, g32p_row21_traceSegment_101_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 850 15 15, g32p_row21_traceSegment_101_0850_0015, g32p_row21_traceSegment_101_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 880 15 16, g32p_row21_traceSegment_101_0880_0015, g32p_row21_traceSegment_101_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 850 30 31, g32p_row21_traceSegment_101_0850_0030, g32p_row21_traceSegment_101_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_101 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 911 15 15, g32p_row21_traceSegment_101_0911_0015, g32p_row21_traceSegment_101_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_101 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_101 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_101_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_101 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 941 15 16, g32p_row21_traceSegment_101_0941_0015, g32p_row21_traceSegment_101_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_101 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 911 30 31, g32p_row21_traceSegment_101_0911_0030, g32p_row21_traceSegment_101_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_101 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 850 61 61, g32p_row21_traceSegment_101_0850_0061, g32p_row21_traceSegment_101_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_101 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 729 121 122, g32p_row21_traceSegment_101_0729_0121, g32p_row21_traceSegment_101_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_101 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 486 243 243, g32p_row21_traceSegment_101_0486_0243, g32p_row21_traceSegment_101_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_101_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_101 0 972 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_101 0 486 486, g32p_row21_traceSegment_101_0000_0486, g32p_row21_traceSegment_101_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 101 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_101_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row21_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 97) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 97) (g32p_literalTraceValue 20 97)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_097]
  decide +kernel

theorem g32p_row21_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 98) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 98) (g32p_literalTraceValue 20 98)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row21_traceCoefficients_098]
  decide +kernel

theorem g32p_row21_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 99) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 99) (g32p_literalTraceValue 20 99)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_099]
  decide +kernel

theorem g32p_row21_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 100) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 100) (g32p_literalTraceValue 20 100)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_100]
  decide +kernel

theorem g32p_row21_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 101) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 101) (g32p_literalTraceValue 20 101)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row21_traceCoefficients_101]
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

def g32p_row21_generatorIndex : Fin 8 → Fin 408 :=
  ![20, 71, 122, 173, 244, 245, 346, 347]

theorem g32p_row21_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup16_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 20 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 20 g32p_row21_supplierClass
    g32p_row21_supplierClass_isConj g32p_supplierGroup16_support g32p_row21_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row21_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup16_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row21_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 20 c false (g32p_row21_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 20 c true (g32p_row21_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 20 c false (g32p_row21_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 20 c true (g32p_row21_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 20 c false (g32p_row21_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 20 c false (g32p_row21_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 20 c true (g32p_row21_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 20 c true (g32p_row21_coinduced_zero c hc true) 3

theorem g32p_row21_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup16_support →
      g32p_literalTraceValue (g32p_row21_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row21_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup16_support →
      g32p_literalTraceValue (g32p_row21_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row21_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup16_support →
      g32p_literalTraceValue (g32p_row21_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row21_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup16_support →
      g32p_literalTraceValue (g32p_row21_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row21_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup16_support →
      g32p_literalTraceValue (g32p_row21_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row21_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup16_support →
      g32p_literalTraceValue (g32p_row21_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row21_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup16_support →
      g32p_literalTraceValue (g32p_row21_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row21_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup16_support) :
    g32p_literalTraceValue (g32p_row21_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup16_support →
    g32p_literalTraceValue (g32p_row21_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row21_zeroTrace_block_00 r k
  · exact g32p_row21_zeroTrace_block_01 r k
  · exact g32p_row21_zeroTrace_block_02 r k
  · exact g32p_row21_zeroTrace_block_03 r k
  · exact g32p_row21_zeroTrace_block_04 r k
  · exact g32p_row21_zeroTrace_block_05 r k
  · exact g32p_row21_zeroTrace_block_06 r k

theorem g32p_row21_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup16_support) :
    (g32p_recordedInductionGenerators (g32p_row21_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row21_generatorIndex k) c) := by
  rw [g32p_row21_recordedGenerator_zero c hc k, g32p_row21_zeroTrace_arithmetic c k hc]
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

def g32p_row21_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [11664] else [3888])) else (if i.val < 4 then [3888] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [972] else (if i.val < 8 then [] else [3888])) else (if i.val < 10 then [972] else (if i.val < 11 then [972] else [1944])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [3888] else [1944]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [1944] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [7776] else [])) else (if i.val < 36 then (if i.val < 35 then [] else [7776]) else (if i.val < 37 then [] else [155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [972])) else (if i.val < 42 then [] else (if i.val < 43 then [] else [1944]))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [972] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [972])) else (if i.val < 55 then [] else (if i.val < 56 then [] else [1944]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [3888] else [31104])) else (if i.val < 67 then [] else (if i.val < 68 then [11664] else [972]))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [972] else [972])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else [972]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [1944])) else (if i.val < 80 then [3888] else (if i.val < 81 then [] else [3888]))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [972])) else (if i.val < 87 then (if i.val < 86 then [] else [972]) else (if i.val < 88 then [3888] else [3888])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [3888] else (if i.val < 91 then [] else [3888])) else (if i.val < 93 then [] else (if i.val < 94 then [3888] else []))) else (if i.val < 98 then (if i.val < 96 then [11664] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [11664] else []) else (if i.val < 101 then [] else [155520])))))))

theorem g32p_row21_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup16_support) :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) c) (g32p_literalTraceValue 20 c)
      [1, 1, 1] (g32p_row21_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row21_tracePolynomial_000
  · exact g32p_row21_tracePolynomial_001
  · exact g32p_row21_tracePolynomial_002
  · exact g32p_row21_tracePolynomial_003
  · exact g32p_row21_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_008
  · exact g32p_row21_tracePolynomial_009
  · exact g32p_row21_tracePolynomial_010
  · exact g32p_row21_tracePolynomial_011
  · exact g32p_row21_tracePolynomial_012
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_014
  · exact g32p_row21_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_018
  · exact g32p_row21_tracePolynomial_019
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_023
  · exact g32p_row21_tracePolynomial_024
  · exact g32p_row21_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_028
  · exact g32p_row21_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_032
  · exact g32p_row21_tracePolynomial_033
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_035
  · exact g32p_row21_tracePolynomial_036
  · exact g32p_row21_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_039
  · exact g32p_row21_tracePolynomial_040
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_042
  · exact g32p_row21_tracePolynomial_043
  · exact g32p_row21_tracePolynomial_044
  · exact g32p_row21_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_050
  · exact g32p_row21_tracePolynomial_051
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_053
  · exact g32p_row21_tracePolynomial_054
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_062
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_064
  · exact g32p_row21_tracePolynomial_065
  · exact g32p_row21_tracePolynomial_066
  · exact g32p_row21_tracePolynomial_067
  · exact g32p_row21_tracePolynomial_068
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_070
  · exact g32p_row21_tracePolynomial_071
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_074
  · exact g32p_row21_tracePolynomial_075
  · exact g32p_row21_tracePolynomial_076
  · exact g32p_row21_tracePolynomial_077
  · exact g32p_row21_tracePolynomial_078
  · exact g32p_row21_tracePolynomial_079
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_081
  · exact g32p_row21_tracePolynomial_082
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_084
  · exact g32p_row21_tracePolynomial_085
  · exact g32p_row21_tracePolynomial_086
  · exact g32p_row21_tracePolynomial_087
  · exact g32p_row21_tracePolynomial_088
  · exact g32p_row21_tracePolynomial_089
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_091
  · exact g32p_row21_tracePolynomial_092
  · exact g32p_row21_tracePolynomial_093
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup16_support) hc)
  · exact g32p_row21_tracePolynomial_095
  · exact g32p_row21_tracePolynomial_096
  · exact g32p_row21_tracePolynomial_097
  · exact g32p_row21_tracePolynomial_098
  · exact g32p_row21_tracePolynomial_099
  · exact g32p_row21_tracePolynomial_100
  · exact g32p_row21_tracePolynomial_101

theorem g32p_row21_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 20 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 20 c) := by
  by_cases hc : c ∈ g32p_supplierGroup16_support
  · have hclass (j : Fin 972) :
        IsConj (g32p_literalRepresentative c) (g32p_row21_groupEquiv j : g32p_G) ↔
          g32p_row21_supplierClassifier j = c := by
      simpa only [g32p_row21_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row21_supplierClass_iff (g32p_row21_groupEquiv j) c
    have hχ (j : Fin 972) :
        (g32p_recordedSupplierCharacters 20 (g32p_row21_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row21_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 20 (show (g32p_recordedSuppliers 20).H from g32p_row21_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row21_characterValues (g32p_row21_groupEquiv.symm (g32p_row21_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 20).H (g32p_recordedSupplierCharacters 20)
      (g32p_literalRepresentative c) g32p_row21_groupEquiv g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) c 3 972
      (g32p_literalCentralizer c) (g32p_literalTraceValue 20 c) [1, 1, 1]
      (g32p_row21_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row21_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 20)))
      (g32p_row21_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row21_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row21_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
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

theorem g32p_row21_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
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

theorem g32p_row21_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
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

theorem g32p_row21_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
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

theorem g32p_row21_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row21_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row21_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 20 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
