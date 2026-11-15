import HodgeLean.Foundations.Program.G32PropFourSixPacked0385
import HodgeLean.Foundations.Program.G32PropFourSixPacked0382
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row21_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 66) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 66) (g32p_literalTraceValue 20 66)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_066]
  decide +kernel

theorem g32p_row21_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 67) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 67) (g32p_literalTraceValue 20 67)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row21_traceCoefficients_067]
  decide +kernel

theorem g32p_row21_tracePolynomial_068 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 68) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 68) (g32p_literalTraceValue 20 68)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_068]
  decide +kernel

theorem g32p_row21_tracePolynomial_070 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 70) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 70) (g32p_literalTraceValue 20 70)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_070]
  decide +kernel

theorem g32p_row21_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 71) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 71) (g32p_literalTraceValue 20 71)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_071]
  decide +kernel

theorem g32p_row21_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 74) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 74) (g32p_literalTraceValue 20 74)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_074]
  decide +kernel

theorem g32p_row21_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 75) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 75) (g32p_literalTraceValue 20 75)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_075]
  decide +kernel

theorem g32p_row21_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 76) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 76) (g32p_literalTraceValue 20 76)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_076]
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

private def g32p_row21_traceSegment_077 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 77 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_077_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 0 15 15, g32p_row21_traceSegment_077_0000_0015, g32p_row21_traceSegment_077_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 30 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 45 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 30 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 30 15 15, g32p_row21_traceSegment_077_0030_0015, g32p_row21_traceSegment_077_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_077 0 60 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 0 30 30, g32p_row21_traceSegment_077_0000_0030, g32p_row21_traceSegment_077_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 60 15 15, g32p_row21_traceSegment_077_0060_0015, g32p_row21_traceSegment_077_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 90 15 16, g32p_row21_traceSegment_077_0090_0015, g32p_row21_traceSegment_077_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 60 30 31, g32p_row21_traceSegment_077_0060_0030, g32p_row21_traceSegment_077_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_077 0 121 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 0 60 61, g32p_row21_traceSegment_077_0000_0060, g32p_row21_traceSegment_077_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 121 15 15, g32p_row21_traceSegment_077_0121_0015, g32p_row21_traceSegment_077_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 151 15 16, g32p_row21_traceSegment_077_0151_0015, g32p_row21_traceSegment_077_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 121 30 31, g32p_row21_traceSegment_077_0121_0030, g32p_row21_traceSegment_077_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 182 15 15, g32p_row21_traceSegment_077_0182_0015, g32p_row21_traceSegment_077_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 212 15 16, g32p_row21_traceSegment_077_0212_0015, g32p_row21_traceSegment_077_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 182 30 31, g32p_row21_traceSegment_077_0182_0030, g32p_row21_traceSegment_077_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_077 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 121 61 61, g32p_row21_traceSegment_077_0121_0061, g32p_row21_traceSegment_077_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_077 0 243 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 0 121 122, g32p_row21_traceSegment_077_0000_0121, g32p_row21_traceSegment_077_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 243 15 15, g32p_row21_traceSegment_077_0243_0015, g32p_row21_traceSegment_077_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 273 15 15, g32p_row21_traceSegment_077_0273_0015, g32p_row21_traceSegment_077_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_077 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 243 30 30, g32p_row21_traceSegment_077_0243_0030, g32p_row21_traceSegment_077_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 303 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 318 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 303 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 303 15 15, g32p_row21_traceSegment_077_0303_0015, g32p_row21_traceSegment_077_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 333 15 16, g32p_row21_traceSegment_077_0333_0015, g32p_row21_traceSegment_077_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 303 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 303 30 31, g32p_row21_traceSegment_077_0303_0030, g32p_row21_traceSegment_077_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_077 243 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 243 60 61, g32p_row21_traceSegment_077_0243_0060, g32p_row21_traceSegment_077_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 364 15 15, g32p_row21_traceSegment_077_0364_0015, g32p_row21_traceSegment_077_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 394 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 409 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 394 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 394 15 16, g32p_row21_traceSegment_077_0394_0015, g32p_row21_traceSegment_077_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 364 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 364 30 31, g32p_row21_traceSegment_077_0364_0030, g32p_row21_traceSegment_077_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 425 15 15, g32p_row21_traceSegment_077_0425_0015, g32p_row21_traceSegment_077_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 470 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 455 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 455 15 16, g32p_row21_traceSegment_077_0455_0015, g32p_row21_traceSegment_077_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 425 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 425 30 31, g32p_row21_traceSegment_077_0425_0030, g32p_row21_traceSegment_077_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_077 364 122 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 364 61 61, g32p_row21_traceSegment_077_0364_0061, g32p_row21_traceSegment_077_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_077 243 243 = [3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 243 121 122, g32p_row21_traceSegment_077_0243_0121, g32p_row21_traceSegment_077_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_077 0 486 = [3, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 0 243 243, g32p_row21_traceSegment_077_0000_0243, g32p_row21_traceSegment_077_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 486 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 486 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 486 15 15, g32p_row21_traceSegment_077_0486_0015, g32p_row21_traceSegment_077_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 516 15 15, g32p_row21_traceSegment_077_0516_0015, g32p_row21_traceSegment_077_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_077 486 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 486 30 30, g32p_row21_traceSegment_077_0486_0030, g32p_row21_traceSegment_077_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 546 15 15, g32p_row21_traceSegment_077_0546_0015, g32p_row21_traceSegment_077_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 576 15 16, g32p_row21_traceSegment_077_0576_0015, g32p_row21_traceSegment_077_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 546 30 31, g32p_row21_traceSegment_077_0546_0030, g32p_row21_traceSegment_077_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_077 486 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 486 60 61, g32p_row21_traceSegment_077_0486_0060, g32p_row21_traceSegment_077_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 607 15 15, g32p_row21_traceSegment_077_0607_0015, g32p_row21_traceSegment_077_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 637 15 16, g32p_row21_traceSegment_077_0637_0015, g32p_row21_traceSegment_077_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 607 30 31, g32p_row21_traceSegment_077_0607_0030, g32p_row21_traceSegment_077_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 668 15 15, g32p_row21_traceSegment_077_0668_0015, g32p_row21_traceSegment_077_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 698 15 16, g32p_row21_traceSegment_077_0698_0015, g32p_row21_traceSegment_077_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 668 30 31, g32p_row21_traceSegment_077_0668_0030, g32p_row21_traceSegment_077_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_077 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 607 61 61, g32p_row21_traceSegment_077_0607_0061, g32p_row21_traceSegment_077_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_077 486 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 486 121 122, g32p_row21_traceSegment_077_0486_0121, g32p_row21_traceSegment_077_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 729 15 15, g32p_row21_traceSegment_077_0729_0015, g32p_row21_traceSegment_077_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 759 15 15, g32p_row21_traceSegment_077_0759_0015, g32p_row21_traceSegment_077_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_077 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 729 30 30, g32p_row21_traceSegment_077_0729_0030, g32p_row21_traceSegment_077_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 789 15 15, g32p_row21_traceSegment_077_0789_0015, g32p_row21_traceSegment_077_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 819 15 16, g32p_row21_traceSegment_077_0819_0015, g32p_row21_traceSegment_077_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 789 30 31, g32p_row21_traceSegment_077_0789_0030, g32p_row21_traceSegment_077_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_077 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 729 60 61, g32p_row21_traceSegment_077_0729_0060, g32p_row21_traceSegment_077_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 850 15 15, g32p_row21_traceSegment_077_0850_0015, g32p_row21_traceSegment_077_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 880 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 895 16 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 880 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 880 15 16, g32p_row21_traceSegment_077_0880_0015, g32p_row21_traceSegment_077_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 850 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 850 30 31, g32p_row21_traceSegment_077_0850_0030, g32p_row21_traceSegment_077_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 911 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 926 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_077 911 30 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 911 15 15, g32p_row21_traceSegment_077_0911_0015, g32p_row21_traceSegment_077_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_077 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_077 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_077_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_077 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 941 15 16, g32p_row21_traceSegment_077_0941_0015, g32p_row21_traceSegment_077_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_077 911 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 911 30 31, g32p_row21_traceSegment_077_0911_0030, g32p_row21_traceSegment_077_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_077 850 122 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 850 61 61, g32p_row21_traceSegment_077_0850_0061, g32p_row21_traceSegment_077_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_077 729 243 = [6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 729 121 122, g32p_row21_traceSegment_077_0729_0121, g32p_row21_traceSegment_077_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_077 486 486 = [6, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 486 243 243, g32p_row21_traceSegment_077_0486_0243, g32p_row21_traceSegment_077_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_077_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_077 0 972 = [9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_077 0 486 486, g32p_row21_traceSegment_077_0000_0486, g32p_row21_traceSegment_077_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 77 = [9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_077_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_078 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 78 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_078_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 0 15 15, g32p_row21_traceSegment_078_0000_0015, g32p_row21_traceSegment_078_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 30 15 15, g32p_row21_traceSegment_078_0030_0015, g32p_row21_traceSegment_078_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_078 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 0 30 30, g32p_row21_traceSegment_078_0000_0030, g32p_row21_traceSegment_078_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 60 15 15, g32p_row21_traceSegment_078_0060_0015, g32p_row21_traceSegment_078_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 90 15 16, g32p_row21_traceSegment_078_0090_0015, g32p_row21_traceSegment_078_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 60 30 31, g32p_row21_traceSegment_078_0060_0030, g32p_row21_traceSegment_078_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_078 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 0 60 61, g32p_row21_traceSegment_078_0000_0060, g32p_row21_traceSegment_078_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 121 15 15, g32p_row21_traceSegment_078_0121_0015, g32p_row21_traceSegment_078_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 151 15 16, g32p_row21_traceSegment_078_0151_0015, g32p_row21_traceSegment_078_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 121 30 31, g32p_row21_traceSegment_078_0121_0030, g32p_row21_traceSegment_078_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 182 15 15, g32p_row21_traceSegment_078_0182_0015, g32p_row21_traceSegment_078_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 212 15 16, g32p_row21_traceSegment_078_0212_0015, g32p_row21_traceSegment_078_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 182 30 31, g32p_row21_traceSegment_078_0182_0030, g32p_row21_traceSegment_078_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_078 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 121 61 61, g32p_row21_traceSegment_078_0121_0061, g32p_row21_traceSegment_078_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_078 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 0 121 122, g32p_row21_traceSegment_078_0000_0121, g32p_row21_traceSegment_078_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 243 15 15, g32p_row21_traceSegment_078_0243_0015, g32p_row21_traceSegment_078_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 273 15 15, g32p_row21_traceSegment_078_0273_0015, g32p_row21_traceSegment_078_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_078 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 243 30 30, g32p_row21_traceSegment_078_0243_0030, g32p_row21_traceSegment_078_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 303 15 15, g32p_row21_traceSegment_078_0303_0015, g32p_row21_traceSegment_078_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 333 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 348 16 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 333 31 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 333 15 16, g32p_row21_traceSegment_078_0333_0015, g32p_row21_traceSegment_078_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 303 61 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 303 30 31, g32p_row21_traceSegment_078_0303_0030, g32p_row21_traceSegment_078_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_078 243 121 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 243 60 61, g32p_row21_traceSegment_078_0243_0060, g32p_row21_traceSegment_078_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 364 15 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 364 30 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 364 15 15, g32p_row21_traceSegment_078_0364_0015, g32p_row21_traceSegment_078_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 394 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 394 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 394 15 16, g32p_row21_traceSegment_078_0394_0015, g32p_row21_traceSegment_078_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 364 61 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 364 30 31, g32p_row21_traceSegment_078_0364_0030, g32p_row21_traceSegment_078_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 425 15 15, g32p_row21_traceSegment_078_0425_0015, g32p_row21_traceSegment_078_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 455 15 16, g32p_row21_traceSegment_078_0455_0015, g32p_row21_traceSegment_078_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 425 30 31, g32p_row21_traceSegment_078_0425_0030, g32p_row21_traceSegment_078_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_078 364 122 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 364 61 61, g32p_row21_traceSegment_078_0364_0061, g32p_row21_traceSegment_078_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_078 243 243 = [0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 243 121 122, g32p_row21_traceSegment_078_0243_0121, g32p_row21_traceSegment_078_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_078 0 486 = [0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 0 243 243, g32p_row21_traceSegment_078_0000_0243, g32p_row21_traceSegment_078_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 486 15 15, g32p_row21_traceSegment_078_0486_0015, g32p_row21_traceSegment_078_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 516 15 15, g32p_row21_traceSegment_078_0516_0015, g32p_row21_traceSegment_078_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_078 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 486 30 30, g32p_row21_traceSegment_078_0486_0030, g32p_row21_traceSegment_078_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 546 15 15, g32p_row21_traceSegment_078_0546_0015, g32p_row21_traceSegment_078_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 576 15 16, g32p_row21_traceSegment_078_0576_0015, g32p_row21_traceSegment_078_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 546 30 31, g32p_row21_traceSegment_078_0546_0030, g32p_row21_traceSegment_078_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_078 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 486 60 61, g32p_row21_traceSegment_078_0486_0060, g32p_row21_traceSegment_078_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 607 15 15, g32p_row21_traceSegment_078_0607_0015, g32p_row21_traceSegment_078_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 637 15 16, g32p_row21_traceSegment_078_0637_0015, g32p_row21_traceSegment_078_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 607 30 31, g32p_row21_traceSegment_078_0607_0030, g32p_row21_traceSegment_078_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 668 15 15, g32p_row21_traceSegment_078_0668_0015, g32p_row21_traceSegment_078_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 698 15 16, g32p_row21_traceSegment_078_0698_0015, g32p_row21_traceSegment_078_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 668 30 31, g32p_row21_traceSegment_078_0668_0030, g32p_row21_traceSegment_078_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_078 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 607 61 61, g32p_row21_traceSegment_078_0607_0061, g32p_row21_traceSegment_078_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_078 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 486 121 122, g32p_row21_traceSegment_078_0486_0121, g32p_row21_traceSegment_078_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 729 15 15, g32p_row21_traceSegment_078_0729_0015, g32p_row21_traceSegment_078_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 759 15 15, g32p_row21_traceSegment_078_0759_0015, g32p_row21_traceSegment_078_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_078 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 729 30 30, g32p_row21_traceSegment_078_0729_0030, g32p_row21_traceSegment_078_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 789 15 15, g32p_row21_traceSegment_078_0789_0015, g32p_row21_traceSegment_078_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 819 15 16, g32p_row21_traceSegment_078_0819_0015, g32p_row21_traceSegment_078_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 789 30 31, g32p_row21_traceSegment_078_0789_0030, g32p_row21_traceSegment_078_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_078 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 729 60 61, g32p_row21_traceSegment_078_0729_0060, g32p_row21_traceSegment_078_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 850 15 15, g32p_row21_traceSegment_078_0850_0015, g32p_row21_traceSegment_078_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 880 15 16, g32p_row21_traceSegment_078_0880_0015, g32p_row21_traceSegment_078_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 850 30 31, g32p_row21_traceSegment_078_0850_0030, g32p_row21_traceSegment_078_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_078 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 911 15 15, g32p_row21_traceSegment_078_0911_0015, g32p_row21_traceSegment_078_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_078 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_078 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_078_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_078 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 941 15 16, g32p_row21_traceSegment_078_0941_0015, g32p_row21_traceSegment_078_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_078 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 911 30 31, g32p_row21_traceSegment_078_0911_0030, g32p_row21_traceSegment_078_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_078 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 850 61 61, g32p_row21_traceSegment_078_0850_0061, g32p_row21_traceSegment_078_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_078 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 729 121 122, g32p_row21_traceSegment_078_0729_0121, g32p_row21_traceSegment_078_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_078 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 486 243 243, g32p_row21_traceSegment_078_0486_0243, g32p_row21_traceSegment_078_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_078_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_078 0 972 = [0, 3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_078 0 486 486, g32p_row21_traceSegment_078_0000_0486, g32p_row21_traceSegment_078_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 78 = [0, 3, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_078_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_079 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 79 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_079_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 0 15 15, g32p_row21_traceSegment_079_0000_0015, g32p_row21_traceSegment_079_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 30 15 15, g32p_row21_traceSegment_079_0030_0015, g32p_row21_traceSegment_079_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_079 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 0 30 30, g32p_row21_traceSegment_079_0000_0030, g32p_row21_traceSegment_079_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 60 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 75 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 60 30 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 60 15 15, g32p_row21_traceSegment_079_0060_0015, g32p_row21_traceSegment_079_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 90 15 16, g32p_row21_traceSegment_079_0090_0015, g32p_row21_traceSegment_079_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 60 61 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 60 30 31, g32p_row21_traceSegment_079_0060_0030, g32p_row21_traceSegment_079_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_079 0 121 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 0 60 61, g32p_row21_traceSegment_079_0000_0060, g32p_row21_traceSegment_079_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 121 15 15, g32p_row21_traceSegment_079_0121_0015, g32p_row21_traceSegment_079_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 151 15 16, g32p_row21_traceSegment_079_0151_0015, g32p_row21_traceSegment_079_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 121 30 31, g32p_row21_traceSegment_079_0121_0030, g32p_row21_traceSegment_079_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 197 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 182 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 182 15 15, g32p_row21_traceSegment_079_0182_0015, g32p_row21_traceSegment_079_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 212 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 227 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 212 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 212 15 16, g32p_row21_traceSegment_079_0212_0015, g32p_row21_traceSegment_079_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 182 61 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 182 30 31, g32p_row21_traceSegment_079_0182_0030, g32p_row21_traceSegment_079_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_079 121 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 121 61 61, g32p_row21_traceSegment_079_0121_0061, g32p_row21_traceSegment_079_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_079 0 243 = [2, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 0 121 122, g32p_row21_traceSegment_079_0000_0121, g32p_row21_traceSegment_079_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 243 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 243 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 243 15 15, g32p_row21_traceSegment_079_0243_0015, g32p_row21_traceSegment_079_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 273 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 273 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 273 15 15, g32p_row21_traceSegment_079_0273_0015, g32p_row21_traceSegment_079_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_079 243 60 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 243 30 30, g32p_row21_traceSegment_079_0243_0030, g32p_row21_traceSegment_079_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 303 15 15, g32p_row21_traceSegment_079_0303_0015, g32p_row21_traceSegment_079_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 333 15 16, g32p_row21_traceSegment_079_0333_0015, g32p_row21_traceSegment_079_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 303 30 31, g32p_row21_traceSegment_079_0303_0030, g32p_row21_traceSegment_079_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_079 243 121 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 243 60 61, g32p_row21_traceSegment_079_0243_0060, g32p_row21_traceSegment_079_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 364 15 15, g32p_row21_traceSegment_079_0364_0015, g32p_row21_traceSegment_079_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 394 15 16, g32p_row21_traceSegment_079_0394_0015, g32p_row21_traceSegment_079_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 364 30 31, g32p_row21_traceSegment_079_0364_0030, g32p_row21_traceSegment_079_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 425 15 15, g32p_row21_traceSegment_079_0425_0015, g32p_row21_traceSegment_079_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 455 15 16, g32p_row21_traceSegment_079_0455_0015, g32p_row21_traceSegment_079_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 425 30 31, g32p_row21_traceSegment_079_0425_0030, g32p_row21_traceSegment_079_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_079 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 364 61 61, g32p_row21_traceSegment_079_0364_0061, g32p_row21_traceSegment_079_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_079 243 243 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 243 121 122, g32p_row21_traceSegment_079_0243_0121, g32p_row21_traceSegment_079_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_079 0 486 = [2, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 0 243 243, g32p_row21_traceSegment_079_0000_0243, g32p_row21_traceSegment_079_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 486 15 15, g32p_row21_traceSegment_079_0486_0015, g32p_row21_traceSegment_079_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 516 15 15, g32p_row21_traceSegment_079_0516_0015, g32p_row21_traceSegment_079_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_079 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 486 30 30, g32p_row21_traceSegment_079_0486_0030, g32p_row21_traceSegment_079_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 546 15 15, g32p_row21_traceSegment_079_0546_0015, g32p_row21_traceSegment_079_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 576 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 591 16 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 576 31 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 576 15 16, g32p_row21_traceSegment_079_0576_0015, g32p_row21_traceSegment_079_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 546 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 546 30 31, g32p_row21_traceSegment_079_0546_0030, g32p_row21_traceSegment_079_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_079 486 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 486 60 61, g32p_row21_traceSegment_079_0486_0060, g32p_row21_traceSegment_079_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 622 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 607 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 607 15 15, g32p_row21_traceSegment_079_0607_0015, g32p_row21_traceSegment_079_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 652 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 637 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 637 15 16, g32p_row21_traceSegment_079_0637_0015, g32p_row21_traceSegment_079_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 607 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 607 30 31, g32p_row21_traceSegment_079_0607_0030, g32p_row21_traceSegment_079_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 668 15 15, g32p_row21_traceSegment_079_0668_0015, g32p_row21_traceSegment_079_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 698 15 16, g32p_row21_traceSegment_079_0698_0015, g32p_row21_traceSegment_079_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 668 30 31, g32p_row21_traceSegment_079_0668_0030, g32p_row21_traceSegment_079_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_079 607 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 607 61 61, g32p_row21_traceSegment_079_0607_0061, g32p_row21_traceSegment_079_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_079 486 243 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 486 121 122, g32p_row21_traceSegment_079_0486_0121, g32p_row21_traceSegment_079_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 729 15 15, g32p_row21_traceSegment_079_0729_0015, g32p_row21_traceSegment_079_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 774 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 759 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 759 15 15, g32p_row21_traceSegment_079_0759_0015, g32p_row21_traceSegment_079_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_079 729 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 729 30 30, g32p_row21_traceSegment_079_0729_0030, g32p_row21_traceSegment_079_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 789 15 15, g32p_row21_traceSegment_079_0789_0015, g32p_row21_traceSegment_079_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 819 15 16, g32p_row21_traceSegment_079_0819_0015, g32p_row21_traceSegment_079_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 789 30 31, g32p_row21_traceSegment_079_0789_0030, g32p_row21_traceSegment_079_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_079 729 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 729 60 61, g32p_row21_traceSegment_079_0729_0060, g32p_row21_traceSegment_079_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 850 15 15, g32p_row21_traceSegment_079_0850_0015, g32p_row21_traceSegment_079_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 895 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 880 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 880 15 16, g32p_row21_traceSegment_079_0880_0015, g32p_row21_traceSegment_079_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 850 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 850 30 31, g32p_row21_traceSegment_079_0850_0030, g32p_row21_traceSegment_079_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 911 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_079 911 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 911 15 15, g32p_row21_traceSegment_079_0911_0015, g32p_row21_traceSegment_079_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_079 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_079 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_079_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_079 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 941 15 16, g32p_row21_traceSegment_079_0941_0015, g32p_row21_traceSegment_079_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_079 911 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 911 30 31, g32p_row21_traceSegment_079_0911_0030, g32p_row21_traceSegment_079_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_079 850 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 850 61 61, g32p_row21_traceSegment_079_0850_0061, g32p_row21_traceSegment_079_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_079 729 243 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 729 121 122, g32p_row21_traceSegment_079_0729_0121, g32p_row21_traceSegment_079_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_079 486 486 = [7, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 486 243 243, g32p_row21_traceSegment_079_0486_0243, g32p_row21_traceSegment_079_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_079_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_079 0 972 = [9, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_079 0 486 486, g32p_row21_traceSegment_079_0000_0486, g32p_row21_traceSegment_079_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 79 = [9, 0, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_079_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_081 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 81 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_081_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 0 15 15, g32p_row21_traceSegment_081_0000_0015, g32p_row21_traceSegment_081_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 30 15 15, g32p_row21_traceSegment_081_0030_0015, g32p_row21_traceSegment_081_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_081 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 0 30 30, g32p_row21_traceSegment_081_0000_0030, g32p_row21_traceSegment_081_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 75 15 = [0, 3, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 60 30 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 60 15 15, g32p_row21_traceSegment_081_0060_0015, g32p_row21_traceSegment_081_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 90 15 16, g32p_row21_traceSegment_081_0090_0015, g32p_row21_traceSegment_081_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 60 61 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 60 30 31, g32p_row21_traceSegment_081_0060_0030, g32p_row21_traceSegment_081_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_081 0 121 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 0 60 61, g32p_row21_traceSegment_081_0000_0060, g32p_row21_traceSegment_081_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 121 15 15, g32p_row21_traceSegment_081_0121_0015, g32p_row21_traceSegment_081_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 151 15 16, g32p_row21_traceSegment_081_0151_0015, g32p_row21_traceSegment_081_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 121 30 31, g32p_row21_traceSegment_081_0121_0030, g32p_row21_traceSegment_081_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 182 15 15, g32p_row21_traceSegment_081_0182_0015, g32p_row21_traceSegment_081_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 212 15 16, g32p_row21_traceSegment_081_0212_0015, g32p_row21_traceSegment_081_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 182 30 31, g32p_row21_traceSegment_081_0182_0030, g32p_row21_traceSegment_081_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_081 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 121 61 61, g32p_row21_traceSegment_081_0121_0061, g32p_row21_traceSegment_081_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_081 0 243 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 0 121 122, g32p_row21_traceSegment_081_0000_0121, g32p_row21_traceSegment_081_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 243 15 15, g32p_row21_traceSegment_081_0243_0015, g32p_row21_traceSegment_081_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 288 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 273 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 273 15 15, g32p_row21_traceSegment_081_0273_0015, g32p_row21_traceSegment_081_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_081 243 60 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 243 30 30, g32p_row21_traceSegment_081_0243_0030, g32p_row21_traceSegment_081_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 303 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 318 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 303 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 303 15 15, g32p_row21_traceSegment_081_0303_0015, g32p_row21_traceSegment_081_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 333 15 16, g32p_row21_traceSegment_081_0333_0015, g32p_row21_traceSegment_081_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 303 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 303 30 31, g32p_row21_traceSegment_081_0303_0030, g32p_row21_traceSegment_081_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_081 243 121 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 243 60 61, g32p_row21_traceSegment_081_0243_0060, g32p_row21_traceSegment_081_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 364 15 15, g32p_row21_traceSegment_081_0364_0015, g32p_row21_traceSegment_081_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 394 15 16, g32p_row21_traceSegment_081_0394_0015, g32p_row21_traceSegment_081_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 364 30 31, g32p_row21_traceSegment_081_0364_0030, g32p_row21_traceSegment_081_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 425 15 15, g32p_row21_traceSegment_081_0425_0015, g32p_row21_traceSegment_081_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 455 15 16, g32p_row21_traceSegment_081_0455_0015, g32p_row21_traceSegment_081_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 425 30 31, g32p_row21_traceSegment_081_0425_0030, g32p_row21_traceSegment_081_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_081 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 364 61 61, g32p_row21_traceSegment_081_0364_0061, g32p_row21_traceSegment_081_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_081 243 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 243 121 122, g32p_row21_traceSegment_081_0243_0121, g32p_row21_traceSegment_081_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_081 0 486 = [0, 3, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 0 243 243, g32p_row21_traceSegment_081_0000_0243, g32p_row21_traceSegment_081_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 486 15 15, g32p_row21_traceSegment_081_0486_0015, g32p_row21_traceSegment_081_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 516 15 15, g32p_row21_traceSegment_081_0516_0015, g32p_row21_traceSegment_081_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_081 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 486 30 30, g32p_row21_traceSegment_081_0486_0030, g32p_row21_traceSegment_081_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 546 15 15, g32p_row21_traceSegment_081_0546_0015, g32p_row21_traceSegment_081_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 591 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 576 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 576 15 16, g32p_row21_traceSegment_081_0576_0015, g32p_row21_traceSegment_081_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 546 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 546 30 31, g32p_row21_traceSegment_081_0546_0030, g32p_row21_traceSegment_081_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_081 486 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 486 60 61, g32p_row21_traceSegment_081_0486_0060, g32p_row21_traceSegment_081_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 607 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 622 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 607 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 607 15 15, g32p_row21_traceSegment_081_0607_0015, g32p_row21_traceSegment_081_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 652 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 637 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 637 15 16, g32p_row21_traceSegment_081_0637_0015, g32p_row21_traceSegment_081_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 607 61 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 607 30 31, g32p_row21_traceSegment_081_0607_0030, g32p_row21_traceSegment_081_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 668 15 15, g32p_row21_traceSegment_081_0668_0015, g32p_row21_traceSegment_081_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 698 15 16, g32p_row21_traceSegment_081_0698_0015, g32p_row21_traceSegment_081_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 668 30 31, g32p_row21_traceSegment_081_0668_0030, g32p_row21_traceSegment_081_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_081 607 122 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 607 61 61, g32p_row21_traceSegment_081_0607_0061, g32p_row21_traceSegment_081_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_081 486 243 = [0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 486 121 122, g32p_row21_traceSegment_081_0486_0121, g32p_row21_traceSegment_081_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 729 15 15, g32p_row21_traceSegment_081_0729_0015, g32p_row21_traceSegment_081_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 759 15 15, g32p_row21_traceSegment_081_0759_0015, g32p_row21_traceSegment_081_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_081 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 729 30 30, g32p_row21_traceSegment_081_0729_0030, g32p_row21_traceSegment_081_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 789 15 15, g32p_row21_traceSegment_081_0789_0015, g32p_row21_traceSegment_081_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 819 15 16, g32p_row21_traceSegment_081_0819_0015, g32p_row21_traceSegment_081_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 789 30 31, g32p_row21_traceSegment_081_0789_0030, g32p_row21_traceSegment_081_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_081 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 729 60 61, g32p_row21_traceSegment_081_0729_0060, g32p_row21_traceSegment_081_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 850 15 15, g32p_row21_traceSegment_081_0850_0015, g32p_row21_traceSegment_081_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 880 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 895 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 880 31 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 880 15 16, g32p_row21_traceSegment_081_0880_0015, g32p_row21_traceSegment_081_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 850 61 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 850 30 31, g32p_row21_traceSegment_081_0850_0030, g32p_row21_traceSegment_081_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 911 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_081 911 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 911 15 15, g32p_row21_traceSegment_081_0911_0015, g32p_row21_traceSegment_081_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_081 941 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_081 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_081_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_081 941 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 941 15 16, g32p_row21_traceSegment_081_0941_0015, g32p_row21_traceSegment_081_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_081 911 61 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 911 30 31, g32p_row21_traceSegment_081_0911_0030, g32p_row21_traceSegment_081_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_081 850 122 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 850 61 61, g32p_row21_traceSegment_081_0850_0061, g32p_row21_traceSegment_081_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_081 729 243 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 729 121 122, g32p_row21_traceSegment_081_0729_0121, g32p_row21_traceSegment_081_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_081 486 486 = [0, 6, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 486 243 243, g32p_row21_traceSegment_081_0486_0243, g32p_row21_traceSegment_081_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_081_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_081 0 972 = [0, 9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_081 0 486 486, g32p_row21_traceSegment_081_0000_0486, g32p_row21_traceSegment_081_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 81 = [0, 9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_081_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_082 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 82 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_082_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 15 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 0 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 0 15 15, g32p_row21_traceSegment_082_0000_0015, g32p_row21_traceSegment_082_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 30 15 15, g32p_row21_traceSegment_082_0030_0015, g32p_row21_traceSegment_082_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_082 0 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 0 30 30, g32p_row21_traceSegment_082_0000_0030, g32p_row21_traceSegment_082_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 60 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 60 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 60 15 15, g32p_row21_traceSegment_082_0060_0015, g32p_row21_traceSegment_082_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 90 15 16, g32p_row21_traceSegment_082_0090_0015, g32p_row21_traceSegment_082_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 60 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 60 30 31, g32p_row21_traceSegment_082_0060_0030, g32p_row21_traceSegment_082_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_082 0 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 0 60 61, g32p_row21_traceSegment_082_0000_0060, g32p_row21_traceSegment_082_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 121 15 15, g32p_row21_traceSegment_082_0121_0015, g32p_row21_traceSegment_082_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 151 15 16, g32p_row21_traceSegment_082_0151_0015, g32p_row21_traceSegment_082_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 121 30 31, g32p_row21_traceSegment_082_0121_0030, g32p_row21_traceSegment_082_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 182 15 15, g32p_row21_traceSegment_082_0182_0015, g32p_row21_traceSegment_082_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 212 15 16, g32p_row21_traceSegment_082_0212_0015, g32p_row21_traceSegment_082_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 182 30 31, g32p_row21_traceSegment_082_0182_0030, g32p_row21_traceSegment_082_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_082 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 121 61 61, g32p_row21_traceSegment_082_0121_0061, g32p_row21_traceSegment_082_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_082 0 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 0 121 122, g32p_row21_traceSegment_082_0000_0121, g32p_row21_traceSegment_082_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 243 15 15, g32p_row21_traceSegment_082_0243_0015, g32p_row21_traceSegment_082_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 273 15 15, g32p_row21_traceSegment_082_0273_0015, g32p_row21_traceSegment_082_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_082 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 243 30 30, g32p_row21_traceSegment_082_0243_0030, g32p_row21_traceSegment_082_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 303 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 303 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 303 15 15, g32p_row21_traceSegment_082_0303_0015, g32p_row21_traceSegment_082_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 333 15 16, g32p_row21_traceSegment_082_0333_0015, g32p_row21_traceSegment_082_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 303 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 303 30 31, g32p_row21_traceSegment_082_0303_0030, g32p_row21_traceSegment_082_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_082 243 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 243 60 61, g32p_row21_traceSegment_082_0243_0060, g32p_row21_traceSegment_082_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 364 15 15, g32p_row21_traceSegment_082_0364_0015, g32p_row21_traceSegment_082_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 394 15 16, g32p_row21_traceSegment_082_0394_0015, g32p_row21_traceSegment_082_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 364 30 31, g32p_row21_traceSegment_082_0364_0030, g32p_row21_traceSegment_082_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 425 15 15, g32p_row21_traceSegment_082_0425_0015, g32p_row21_traceSegment_082_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 455 15 16, g32p_row21_traceSegment_082_0455_0015, g32p_row21_traceSegment_082_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 425 30 31, g32p_row21_traceSegment_082_0425_0030, g32p_row21_traceSegment_082_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_082 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 364 61 61, g32p_row21_traceSegment_082_0364_0061, g32p_row21_traceSegment_082_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_082 243 243 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 243 121 122, g32p_row21_traceSegment_082_0243_0121, g32p_row21_traceSegment_082_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_082 0 486 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 0 243 243, g32p_row21_traceSegment_082_0000_0243, g32p_row21_traceSegment_082_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 486 15 15, g32p_row21_traceSegment_082_0486_0015, g32p_row21_traceSegment_082_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 516 15 15, g32p_row21_traceSegment_082_0516_0015, g32p_row21_traceSegment_082_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_082 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 486 30 30, g32p_row21_traceSegment_082_0486_0030, g32p_row21_traceSegment_082_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 561 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 546 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 546 15 15, g32p_row21_traceSegment_082_0546_0015, g32p_row21_traceSegment_082_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 576 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 591 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 576 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 576 15 16, g32p_row21_traceSegment_082_0576_0015, g32p_row21_traceSegment_082_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 546 61 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 546 30 31, g32p_row21_traceSegment_082_0546_0030, g32p_row21_traceSegment_082_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_082 486 121 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 486 60 61, g32p_row21_traceSegment_082_0486_0060, g32p_row21_traceSegment_082_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 607 15 15, g32p_row21_traceSegment_082_0607_0015, g32p_row21_traceSegment_082_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 637 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 637 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 637 15 16, g32p_row21_traceSegment_082_0637_0015, g32p_row21_traceSegment_082_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 607 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 607 30 31, g32p_row21_traceSegment_082_0607_0030, g32p_row21_traceSegment_082_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 668 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 668 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 668 15 15, g32p_row21_traceSegment_082_0668_0015, g32p_row21_traceSegment_082_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 698 15 16, g32p_row21_traceSegment_082_0698_0015, g32p_row21_traceSegment_082_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 668 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 668 30 31, g32p_row21_traceSegment_082_0668_0030, g32p_row21_traceSegment_082_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_082 607 122 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 607 61 61, g32p_row21_traceSegment_082_0607_0061, g32p_row21_traceSegment_082_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_082 486 243 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 486 121 122, g32p_row21_traceSegment_082_0486_0121, g32p_row21_traceSegment_082_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 729 15 15, g32p_row21_traceSegment_082_0729_0015, g32p_row21_traceSegment_082_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 759 15 15, g32p_row21_traceSegment_082_0759_0015, g32p_row21_traceSegment_082_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_082 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 729 30 30, g32p_row21_traceSegment_082_0729_0030, g32p_row21_traceSegment_082_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 789 15 15, g32p_row21_traceSegment_082_0789_0015, g32p_row21_traceSegment_082_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 834 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 819 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 819 15 16, g32p_row21_traceSegment_082_0819_0015, g32p_row21_traceSegment_082_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 789 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 789 30 31, g32p_row21_traceSegment_082_0789_0030, g32p_row21_traceSegment_082_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_082 729 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 729 60 61, g32p_row21_traceSegment_082_0729_0060, g32p_row21_traceSegment_082_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 850 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 865 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 850 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 850 15 15, g32p_row21_traceSegment_082_0850_0015, g32p_row21_traceSegment_082_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 880 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 895 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 880 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 880 15 16, g32p_row21_traceSegment_082_0880_0015, g32p_row21_traceSegment_082_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 850 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 850 30 31, g32p_row21_traceSegment_082_0850_0030, g32p_row21_traceSegment_082_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_082 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 911 15 15, g32p_row21_traceSegment_082_0911_0015, g32p_row21_traceSegment_082_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_082 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_082 956 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_082_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_082 941 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 941 15 16, g32p_row21_traceSegment_082_0941_0015, g32p_row21_traceSegment_082_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_082 911 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 911 30 31, g32p_row21_traceSegment_082_0911_0030, g32p_row21_traceSegment_082_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_082 850 122 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 850 61 61, g32p_row21_traceSegment_082_0850_0061, g32p_row21_traceSegment_082_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_082 729 243 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 729 121 122, g32p_row21_traceSegment_082_0729_0121, g32p_row21_traceSegment_082_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_082 486 486 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 486 243 243, g32p_row21_traceSegment_082_0486_0243, g32p_row21_traceSegment_082_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_082_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_082 0 972 = [0, 18] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_082 0 486 486, g32p_row21_traceSegment_082_0000_0486, g32p_row21_traceSegment_082_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 82 = [0, 18] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_082_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_084 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 84 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_084_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 15 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 0 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 0 15 15, g32p_row21_traceSegment_084_0000_0015, g32p_row21_traceSegment_084_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 30 15 15, g32p_row21_traceSegment_084_0030_0015, g32p_row21_traceSegment_084_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_084 0 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 0 30 30, g32p_row21_traceSegment_084_0000_0030, g32p_row21_traceSegment_084_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 75 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 60 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 60 15 15, g32p_row21_traceSegment_084_0060_0015, g32p_row21_traceSegment_084_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 90 15 16, g32p_row21_traceSegment_084_0090_0015, g32p_row21_traceSegment_084_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 60 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 60 30 31, g32p_row21_traceSegment_084_0060_0030, g32p_row21_traceSegment_084_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_084 0 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 0 60 61, g32p_row21_traceSegment_084_0000_0060, g32p_row21_traceSegment_084_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 121 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 121 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 121 15 15, g32p_row21_traceSegment_084_0121_0015, g32p_row21_traceSegment_084_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 151 15 16, g32p_row21_traceSegment_084_0151_0015, g32p_row21_traceSegment_084_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 121 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 121 30 31, g32p_row21_traceSegment_084_0121_0030, g32p_row21_traceSegment_084_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 197 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 182 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 182 15 15, g32p_row21_traceSegment_084_0182_0015, g32p_row21_traceSegment_084_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 212 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 212 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 212 15 16, g32p_row21_traceSegment_084_0212_0015, g32p_row21_traceSegment_084_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 182 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 182 30 31, g32p_row21_traceSegment_084_0182_0030, g32p_row21_traceSegment_084_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_084 121 122 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 121 61 61, g32p_row21_traceSegment_084_0121_0061, g32p_row21_traceSegment_084_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_084 0 243 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 0 121 122, g32p_row21_traceSegment_084_0000_0121, g32p_row21_traceSegment_084_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 243 15 15, g32p_row21_traceSegment_084_0243_0015, g32p_row21_traceSegment_084_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 273 15 15, g32p_row21_traceSegment_084_0273_0015, g32p_row21_traceSegment_084_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_084 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 243 30 30, g32p_row21_traceSegment_084_0243_0030, g32p_row21_traceSegment_084_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 303 15 15, g32p_row21_traceSegment_084_0303_0015, g32p_row21_traceSegment_084_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 333 15 16, g32p_row21_traceSegment_084_0333_0015, g32p_row21_traceSegment_084_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 303 30 31, g32p_row21_traceSegment_084_0303_0030, g32p_row21_traceSegment_084_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_084 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 243 60 61, g32p_row21_traceSegment_084_0243_0060, g32p_row21_traceSegment_084_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 364 15 15, g32p_row21_traceSegment_084_0364_0015, g32p_row21_traceSegment_084_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 394 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 394 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 394 15 16, g32p_row21_traceSegment_084_0394_0015, g32p_row21_traceSegment_084_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 364 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 364 30 31, g32p_row21_traceSegment_084_0364_0030, g32p_row21_traceSegment_084_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 425 15 15, g32p_row21_traceSegment_084_0425_0015, g32p_row21_traceSegment_084_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 455 15 16, g32p_row21_traceSegment_084_0455_0015, g32p_row21_traceSegment_084_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 425 30 31, g32p_row21_traceSegment_084_0425_0030, g32p_row21_traceSegment_084_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_084 364 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 364 61 61, g32p_row21_traceSegment_084_0364_0061, g32p_row21_traceSegment_084_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_084 243 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 243 121 122, g32p_row21_traceSegment_084_0243_0121, g32p_row21_traceSegment_084_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_084 0 486 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 0 243 243, g32p_row21_traceSegment_084_0000_0243, g32p_row21_traceSegment_084_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 486 15 15, g32p_row21_traceSegment_084_0486_0015, g32p_row21_traceSegment_084_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 516 15 15, g32p_row21_traceSegment_084_0516_0015, g32p_row21_traceSegment_084_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_084 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 486 30 30, g32p_row21_traceSegment_084_0486_0030, g32p_row21_traceSegment_084_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 546 15 15, g32p_row21_traceSegment_084_0546_0015, g32p_row21_traceSegment_084_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 576 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 591 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 576 31 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 576 15 16, g32p_row21_traceSegment_084_0576_0015, g32p_row21_traceSegment_084_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 546 61 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 546 30 31, g32p_row21_traceSegment_084_0546_0030, g32p_row21_traceSegment_084_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_084 486 121 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 486 60 61, g32p_row21_traceSegment_084_0486_0060, g32p_row21_traceSegment_084_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 607 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 622 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 607 30 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 607 15 15, g32p_row21_traceSegment_084_0607_0015, g32p_row21_traceSegment_084_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 637 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 637 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 637 15 16, g32p_row21_traceSegment_084_0637_0015, g32p_row21_traceSegment_084_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 607 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 607 30 31, g32p_row21_traceSegment_084_0607_0030, g32p_row21_traceSegment_084_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 668 15 15, g32p_row21_traceSegment_084_0668_0015, g32p_row21_traceSegment_084_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 698 15 16, g32p_row21_traceSegment_084_0698_0015, g32p_row21_traceSegment_084_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 668 30 31, g32p_row21_traceSegment_084_0668_0030, g32p_row21_traceSegment_084_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_084 607 122 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 607 61 61, g32p_row21_traceSegment_084_0607_0061, g32p_row21_traceSegment_084_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_084 486 243 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 486 121 122, g32p_row21_traceSegment_084_0486_0121, g32p_row21_traceSegment_084_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 729 15 15, g32p_row21_traceSegment_084_0729_0015, g32p_row21_traceSegment_084_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 759 15 15, g32p_row21_traceSegment_084_0759_0015, g32p_row21_traceSegment_084_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_084 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 729 30 30, g32p_row21_traceSegment_084_0729_0030, g32p_row21_traceSegment_084_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 789 15 15, g32p_row21_traceSegment_084_0789_0015, g32p_row21_traceSegment_084_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 819 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 819 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 819 15 16, g32p_row21_traceSegment_084_0819_0015, g32p_row21_traceSegment_084_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 789 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 789 30 31, g32p_row21_traceSegment_084_0789_0030, g32p_row21_traceSegment_084_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_084 729 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 729 60 61, g32p_row21_traceSegment_084_0729_0060, g32p_row21_traceSegment_084_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 850 15 15, g32p_row21_traceSegment_084_0850_0015, g32p_row21_traceSegment_084_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 895 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 880 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 880 15 16, g32p_row21_traceSegment_084_0880_0015, g32p_row21_traceSegment_084_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 850 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 850 30 31, g32p_row21_traceSegment_084_0850_0030, g32p_row21_traceSegment_084_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 911 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 926 15 = [0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_084 911 30 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 911 15 15, g32p_row21_traceSegment_084_0911_0015, g32p_row21_traceSegment_084_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_084 941 15 = [3, 4] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_084 956 16 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_084_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_084 941 31 = [3, 4, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 941 15 16, g32p_row21_traceSegment_084_0941_0015, g32p_row21_traceSegment_084_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_084 911 61 = [3, 9, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 911 30 31, g32p_row21_traceSegment_084_0911_0030, g32p_row21_traceSegment_084_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_084 850 122 = [3, 10, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 850 61 61, g32p_row21_traceSegment_084_0850_0061, g32p_row21_traceSegment_084_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_084 729 243 = [3, 11, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 729 121 122, g32p_row21_traceSegment_084_0729_0121, g32p_row21_traceSegment_084_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_084 486 486 = [3, 18, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 486 243 243, g32p_row21_traceSegment_084_0486_0243, g32p_row21_traceSegment_084_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_084_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_084 0 972 = [3, 24, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_084 0 486 486, g32p_row21_traceSegment_084_0000_0486, g32p_row21_traceSegment_084_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 84 = [3, 24, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_084_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_085 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 85 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_085_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 0 15 15, g32p_row21_traceSegment_085_0000_0015, g32p_row21_traceSegment_085_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 30 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 45 15 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 30 30 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 30 15 15, g32p_row21_traceSegment_085_0030_0015, g32p_row21_traceSegment_085_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_085 0 60 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 0 30 30, g32p_row21_traceSegment_085_0000_0030, g32p_row21_traceSegment_085_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 60 15 15, g32p_row21_traceSegment_085_0060_0015, g32p_row21_traceSegment_085_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 90 15 16, g32p_row21_traceSegment_085_0090_0015, g32p_row21_traceSegment_085_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 60 30 31, g32p_row21_traceSegment_085_0060_0030, g32p_row21_traceSegment_085_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_085 0 121 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 0 60 61, g32p_row21_traceSegment_085_0000_0060, g32p_row21_traceSegment_085_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 121 15 15, g32p_row21_traceSegment_085_0121_0015, g32p_row21_traceSegment_085_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 151 15 16, g32p_row21_traceSegment_085_0151_0015, g32p_row21_traceSegment_085_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 121 30 31, g32p_row21_traceSegment_085_0121_0030, g32p_row21_traceSegment_085_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 182 15 15, g32p_row21_traceSegment_085_0182_0015, g32p_row21_traceSegment_085_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 212 15 16, g32p_row21_traceSegment_085_0212_0015, g32p_row21_traceSegment_085_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 182 30 31, g32p_row21_traceSegment_085_0182_0030, g32p_row21_traceSegment_085_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_085 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 121 61 61, g32p_row21_traceSegment_085_0121_0061, g32p_row21_traceSegment_085_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_085 0 243 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 0 121 122, g32p_row21_traceSegment_085_0000_0121, g32p_row21_traceSegment_085_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 243 15 15, g32p_row21_traceSegment_085_0243_0015, g32p_row21_traceSegment_085_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 273 15 15, g32p_row21_traceSegment_085_0273_0015, g32p_row21_traceSegment_085_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_085 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 243 30 30, g32p_row21_traceSegment_085_0243_0030, g32p_row21_traceSegment_085_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 303 15 15, g32p_row21_traceSegment_085_0303_0015, g32p_row21_traceSegment_085_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 333 15 16, g32p_row21_traceSegment_085_0333_0015, g32p_row21_traceSegment_085_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 303 30 31, g32p_row21_traceSegment_085_0303_0030, g32p_row21_traceSegment_085_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_085 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 243 60 61, g32p_row21_traceSegment_085_0243_0060, g32p_row21_traceSegment_085_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 364 15 15, g32p_row21_traceSegment_085_0364_0015, g32p_row21_traceSegment_085_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 409 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 394 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 394 15 16, g32p_row21_traceSegment_085_0394_0015, g32p_row21_traceSegment_085_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 364 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 364 30 31, g32p_row21_traceSegment_085_0364_0030, g32p_row21_traceSegment_085_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 425 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 425 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 425 15 15, g32p_row21_traceSegment_085_0425_0015, g32p_row21_traceSegment_085_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 455 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 470 16 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 455 31 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 455 15 16, g32p_row21_traceSegment_085_0455_0015, g32p_row21_traceSegment_085_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 425 61 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 425 30 31, g32p_row21_traceSegment_085_0425_0030, g32p_row21_traceSegment_085_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_085 364 122 = [1, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 364 61 61, g32p_row21_traceSegment_085_0364_0061, g32p_row21_traceSegment_085_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_085 243 243 = [1, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 243 121 122, g32p_row21_traceSegment_085_0243_0121, g32p_row21_traceSegment_085_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_085 0 486 = [2, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 0 243 243, g32p_row21_traceSegment_085_0000_0243, g32p_row21_traceSegment_085_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 486 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 501 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 486 30 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 486 15 15, g32p_row21_traceSegment_085_0486_0015, g32p_row21_traceSegment_085_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 516 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 516 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 516 15 15, g32p_row21_traceSegment_085_0516_0015, g32p_row21_traceSegment_085_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_085 486 60 = [3, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 486 30 30, g32p_row21_traceSegment_085_0486_0030, g32p_row21_traceSegment_085_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 546 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 561 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 546 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 546 15 15, g32p_row21_traceSegment_085_0546_0015, g32p_row21_traceSegment_085_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 576 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 576 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 576 15 16, g32p_row21_traceSegment_085_0576_0015, g32p_row21_traceSegment_085_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 546 61 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 546 30 31, g32p_row21_traceSegment_085_0546_0030, g32p_row21_traceSegment_085_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_085 486 121 = [6, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 486 60 61, g32p_row21_traceSegment_085_0486_0060, g32p_row21_traceSegment_085_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 607 15 15, g32p_row21_traceSegment_085_0607_0015, g32p_row21_traceSegment_085_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 637 15 16, g32p_row21_traceSegment_085_0637_0015, g32p_row21_traceSegment_085_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 607 30 31, g32p_row21_traceSegment_085_0607_0030, g32p_row21_traceSegment_085_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 668 15 15, g32p_row21_traceSegment_085_0668_0015, g32p_row21_traceSegment_085_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 698 15 16, g32p_row21_traceSegment_085_0698_0015, g32p_row21_traceSegment_085_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 668 30 31, g32p_row21_traceSegment_085_0668_0030, g32p_row21_traceSegment_085_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_085 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 607 61 61, g32p_row21_traceSegment_085_0607_0061, g32p_row21_traceSegment_085_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_085 486 243 = [6, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 486 121 122, g32p_row21_traceSegment_085_0486_0121, g32p_row21_traceSegment_085_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 729 15 15, g32p_row21_traceSegment_085_0729_0015, g32p_row21_traceSegment_085_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 759 15 15, g32p_row21_traceSegment_085_0759_0015, g32p_row21_traceSegment_085_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_085 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 729 30 30, g32p_row21_traceSegment_085_0729_0030, g32p_row21_traceSegment_085_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 789 15 15, g32p_row21_traceSegment_085_0789_0015, g32p_row21_traceSegment_085_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 834 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 819 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 819 15 16, g32p_row21_traceSegment_085_0819_0015, g32p_row21_traceSegment_085_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 789 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 789 30 31, g32p_row21_traceSegment_085_0789_0030, g32p_row21_traceSegment_085_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_085 729 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 729 60 61, g32p_row21_traceSegment_085_0729_0060, g32p_row21_traceSegment_085_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 850 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 850 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 850 15 15, g32p_row21_traceSegment_085_0850_0015, g32p_row21_traceSegment_085_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 880 15 16, g32p_row21_traceSegment_085_0880_0015, g32p_row21_traceSegment_085_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 850 61 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 850 30 31, g32p_row21_traceSegment_085_0850_0030, g32p_row21_traceSegment_085_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_085 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 911 15 15, g32p_row21_traceSegment_085_0911_0015, g32p_row21_traceSegment_085_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_085 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_085 956 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_085_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_085 941 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 941 15 16, g32p_row21_traceSegment_085_0941_0015, g32p_row21_traceSegment_085_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_085 911 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 911 30 31, g32p_row21_traceSegment_085_0911_0030, g32p_row21_traceSegment_085_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_085 850 122 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 850 61 61, g32p_row21_traceSegment_085_0850_0061, g32p_row21_traceSegment_085_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_085 729 243 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 729 121 122, g32p_row21_traceSegment_085_0729_0121, g32p_row21_traceSegment_085_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_085 486 486 = [7, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 486 243 243, g32p_row21_traceSegment_085_0486_0243, g32p_row21_traceSegment_085_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_085_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_085 0 972 = [9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_085 0 486 486, g32p_row21_traceSegment_085_0000_0486, g32p_row21_traceSegment_085_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 85 = [9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_085_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_086 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 86 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_086_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 0 15 15, g32p_row21_traceSegment_086_0000_0015, g32p_row21_traceSegment_086_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 30 15 15, g32p_row21_traceSegment_086_0030_0015, g32p_row21_traceSegment_086_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_086 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 0 30 30, g32p_row21_traceSegment_086_0000_0030, g32p_row21_traceSegment_086_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 60 15 15, g32p_row21_traceSegment_086_0060_0015, g32p_row21_traceSegment_086_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 90 15 16, g32p_row21_traceSegment_086_0090_0015, g32p_row21_traceSegment_086_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 60 30 31, g32p_row21_traceSegment_086_0060_0030, g32p_row21_traceSegment_086_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_086 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 0 60 61, g32p_row21_traceSegment_086_0000_0060, g32p_row21_traceSegment_086_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 121 15 15, g32p_row21_traceSegment_086_0121_0015, g32p_row21_traceSegment_086_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 151 15 = [3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 166 16 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 151 31 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 151 15 16, g32p_row21_traceSegment_086_0151_0015, g32p_row21_traceSegment_086_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 121 61 = [5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 121 30 31, g32p_row21_traceSegment_086_0121_0030, g32p_row21_traceSegment_086_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 182 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 182 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 182 15 15, g32p_row21_traceSegment_086_0182_0015, g32p_row21_traceSegment_086_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 227 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 212 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 212 15 16, g32p_row21_traceSegment_086_0212_0015, g32p_row21_traceSegment_086_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 182 61 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 182 30 31, g32p_row21_traceSegment_086_0182_0030, g32p_row21_traceSegment_086_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_086 121 122 = [6, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 121 61 61, g32p_row21_traceSegment_086_0121_0061, g32p_row21_traceSegment_086_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_086 0 243 = [6, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 0 121 122, g32p_row21_traceSegment_086_0000_0121, g32p_row21_traceSegment_086_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 243 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 258 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 243 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 243 15 15, g32p_row21_traceSegment_086_0243_0015, g32p_row21_traceSegment_086_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 273 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 273 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 273 15 15, g32p_row21_traceSegment_086_0273_0015, g32p_row21_traceSegment_086_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_086 243 60 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 243 30 30, g32p_row21_traceSegment_086_0243_0030, g32p_row21_traceSegment_086_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 303 15 15, g32p_row21_traceSegment_086_0303_0015, g32p_row21_traceSegment_086_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 333 15 16, g32p_row21_traceSegment_086_0333_0015, g32p_row21_traceSegment_086_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 303 30 31, g32p_row21_traceSegment_086_0303_0030, g32p_row21_traceSegment_086_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_086 243 121 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 243 60 61, g32p_row21_traceSegment_086_0243_0060, g32p_row21_traceSegment_086_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 364 15 15, g32p_row21_traceSegment_086_0364_0015, g32p_row21_traceSegment_086_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 394 15 16, g32p_row21_traceSegment_086_0394_0015, g32p_row21_traceSegment_086_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 364 30 31, g32p_row21_traceSegment_086_0364_0030, g32p_row21_traceSegment_086_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 425 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 440 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 425 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 425 15 15, g32p_row21_traceSegment_086_0425_0015, g32p_row21_traceSegment_086_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 455 15 16, g32p_row21_traceSegment_086_0455_0015, g32p_row21_traceSegment_086_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 425 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 425 30 31, g32p_row21_traceSegment_086_0425_0030, g32p_row21_traceSegment_086_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_086 364 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 364 61 61, g32p_row21_traceSegment_086_0364_0061, g32p_row21_traceSegment_086_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_086 243 243 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 243 121 122, g32p_row21_traceSegment_086_0243_0121, g32p_row21_traceSegment_086_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_086 0 486 = [8, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 0 243 243, g32p_row21_traceSegment_086_0000_0243, g32p_row21_traceSegment_086_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 486 15 15, g32p_row21_traceSegment_086_0486_0015, g32p_row21_traceSegment_086_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 516 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 516 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 516 15 15, g32p_row21_traceSegment_086_0516_0015, g32p_row21_traceSegment_086_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_086 486 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 486 30 30, g32p_row21_traceSegment_086_0486_0030, g32p_row21_traceSegment_086_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 546 15 15, g32p_row21_traceSegment_086_0546_0015, g32p_row21_traceSegment_086_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 576 15 16, g32p_row21_traceSegment_086_0576_0015, g32p_row21_traceSegment_086_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 546 30 31, g32p_row21_traceSegment_086_0546_0030, g32p_row21_traceSegment_086_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_086 486 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 486 60 61, g32p_row21_traceSegment_086_0486_0060, g32p_row21_traceSegment_086_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 607 15 15, g32p_row21_traceSegment_086_0607_0015, g32p_row21_traceSegment_086_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 637 15 16, g32p_row21_traceSegment_086_0637_0015, g32p_row21_traceSegment_086_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 607 30 31, g32p_row21_traceSegment_086_0607_0030, g32p_row21_traceSegment_086_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 668 15 15, g32p_row21_traceSegment_086_0668_0015, g32p_row21_traceSegment_086_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 698 15 16, g32p_row21_traceSegment_086_0698_0015, g32p_row21_traceSegment_086_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 668 30 31, g32p_row21_traceSegment_086_0668_0030, g32p_row21_traceSegment_086_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_086 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 607 61 61, g32p_row21_traceSegment_086_0607_0061, g32p_row21_traceSegment_086_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_086 486 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 486 121 122, g32p_row21_traceSegment_086_0486_0121, g32p_row21_traceSegment_086_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 729 15 15, g32p_row21_traceSegment_086_0729_0015, g32p_row21_traceSegment_086_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 774 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 759 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 759 15 15, g32p_row21_traceSegment_086_0759_0015, g32p_row21_traceSegment_086_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_086 729 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 729 30 30, g32p_row21_traceSegment_086_0729_0030, g32p_row21_traceSegment_086_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 789 15 15, g32p_row21_traceSegment_086_0789_0015, g32p_row21_traceSegment_086_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 819 15 16, g32p_row21_traceSegment_086_0819_0015, g32p_row21_traceSegment_086_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 789 30 31, g32p_row21_traceSegment_086_0789_0030, g32p_row21_traceSegment_086_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_086 729 121 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 729 60 61, g32p_row21_traceSegment_086_0729_0060, g32p_row21_traceSegment_086_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 850 15 15, g32p_row21_traceSegment_086_0850_0015, g32p_row21_traceSegment_086_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 895 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 880 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 880 15 16, g32p_row21_traceSegment_086_0880_0015, g32p_row21_traceSegment_086_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 850 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 850 30 31, g32p_row21_traceSegment_086_0850_0030, g32p_row21_traceSegment_086_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_086 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 911 15 15, g32p_row21_traceSegment_086_0911_0015, g32p_row21_traceSegment_086_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_086 941 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_086 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_086_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_086 941 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 941 15 16, g32p_row21_traceSegment_086_0941_0015, g32p_row21_traceSegment_086_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_086 911 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 911 30 31, g32p_row21_traceSegment_086_0911_0030, g32p_row21_traceSegment_086_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_086 850 122 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 850 61 61, g32p_row21_traceSegment_086_0850_0061, g32p_row21_traceSegment_086_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_086 729 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 729 121 122, g32p_row21_traceSegment_086_0729_0121, g32p_row21_traceSegment_086_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_086 486 486 = [1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 486 243 243, g32p_row21_traceSegment_086_0486_0243, g32p_row21_traceSegment_086_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_086_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_086 0 972 = [9, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_086 0 486 486, g32p_row21_traceSegment_086_0000_0486, g32p_row21_traceSegment_086_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 86 = [9, 0, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_086_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row21_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 77) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 77) (g32p_literalTraceValue 20 77)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_077]
  decide +kernel

theorem g32p_row21_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 78) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 78) (g32p_literalTraceValue 20 78)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row21_traceCoefficients_078]
  decide +kernel

theorem g32p_row21_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 79) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 79) (g32p_literalTraceValue 20 79)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_079]
  decide +kernel

theorem g32p_row21_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 81) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 81) (g32p_literalTraceValue 20 81)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row21_traceCoefficients_081]
  decide +kernel

theorem g32p_row21_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 82) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 82) (g32p_literalTraceValue 20 82)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_082]
  decide +kernel

theorem g32p_row21_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 84) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 84) (g32p_literalTraceValue 20 84)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_084]
  decide +kernel

theorem g32p_row21_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 85) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 85) (g32p_literalTraceValue 20 85)
      [1, 1, 1] [] = true := by
  rw [g32p_row21_traceCoefficients_085]
  decide +kernel

theorem g32p_row21_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 972 (g32p_literalCentralizer 86) 3
      (g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 86) (g32p_literalTraceValue 20 86)
      [1, 1, 1] [972] = true := by
  rw [g32p_row21_traceCoefficients_086]
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

private def g32p_row21_traceSegment_087 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 87 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_087_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 0 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 0 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 0 15 15, g32p_row21_traceSegment_087_0000_0015, g32p_row21_traceSegment_087_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 30 15 15, g32p_row21_traceSegment_087_0030_0015, g32p_row21_traceSegment_087_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_087 0 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 0 30 30, g32p_row21_traceSegment_087_0000_0030, g32p_row21_traceSegment_087_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 60 15 15, g32p_row21_traceSegment_087_0060_0015, g32p_row21_traceSegment_087_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 105 16 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 90 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 90 15 16, g32p_row21_traceSegment_087_0090_0015, g32p_row21_traceSegment_087_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 60 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 60 30 31, g32p_row21_traceSegment_087_0060_0030, g32p_row21_traceSegment_087_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_087 0 121 = [3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 0 60 61, g32p_row21_traceSegment_087_0000_0060, g32p_row21_traceSegment_087_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 121 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 121 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 121 15 15, g32p_row21_traceSegment_087_0121_0015, g32p_row21_traceSegment_087_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 151 15 16, g32p_row21_traceSegment_087_0151_0015, g32p_row21_traceSegment_087_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 121 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 121 30 31, g32p_row21_traceSegment_087_0121_0030, g32p_row21_traceSegment_087_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 182 15 15, g32p_row21_traceSegment_087_0182_0015, g32p_row21_traceSegment_087_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 212 15 16, g32p_row21_traceSegment_087_0212_0015, g32p_row21_traceSegment_087_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 182 30 31, g32p_row21_traceSegment_087_0182_0030, g32p_row21_traceSegment_087_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_087 121 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 121 61 61, g32p_row21_traceSegment_087_0121_0061, g32p_row21_traceSegment_087_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_087 0 243 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 0 121 122, g32p_row21_traceSegment_087_0000_0121, g32p_row21_traceSegment_087_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 243 15 15, g32p_row21_traceSegment_087_0243_0015, g32p_row21_traceSegment_087_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 273 15 15, g32p_row21_traceSegment_087_0273_0015, g32p_row21_traceSegment_087_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_087 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 243 30 30, g32p_row21_traceSegment_087_0243_0030, g32p_row21_traceSegment_087_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 303 15 15, g32p_row21_traceSegment_087_0303_0015, g32p_row21_traceSegment_087_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 333 15 16, g32p_row21_traceSegment_087_0333_0015, g32p_row21_traceSegment_087_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 303 30 31, g32p_row21_traceSegment_087_0303_0030, g32p_row21_traceSegment_087_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_087 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 243 60 61, g32p_row21_traceSegment_087_0243_0060, g32p_row21_traceSegment_087_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 364 15 15, g32p_row21_traceSegment_087_0364_0015, g32p_row21_traceSegment_087_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 394 15 16, g32p_row21_traceSegment_087_0394_0015, g32p_row21_traceSegment_087_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 364 30 31, g32p_row21_traceSegment_087_0364_0030, g32p_row21_traceSegment_087_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 425 15 15, g32p_row21_traceSegment_087_0425_0015, g32p_row21_traceSegment_087_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 455 15 16, g32p_row21_traceSegment_087_0455_0015, g32p_row21_traceSegment_087_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 425 30 31, g32p_row21_traceSegment_087_0425_0030, g32p_row21_traceSegment_087_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_087 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 364 61 61, g32p_row21_traceSegment_087_0364_0061, g32p_row21_traceSegment_087_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_087 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 243 121 122, g32p_row21_traceSegment_087_0243_0121, g32p_row21_traceSegment_087_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_087 0 486 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 0 243 243, g32p_row21_traceSegment_087_0000_0243, g32p_row21_traceSegment_087_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 486 15 15, g32p_row21_traceSegment_087_0486_0015, g32p_row21_traceSegment_087_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 516 15 15, g32p_row21_traceSegment_087_0516_0015, g32p_row21_traceSegment_087_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_087 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 486 30 30, g32p_row21_traceSegment_087_0486_0030, g32p_row21_traceSegment_087_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 546 15 15, g32p_row21_traceSegment_087_0546_0015, g32p_row21_traceSegment_087_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 576 15 16, g32p_row21_traceSegment_087_0576_0015, g32p_row21_traceSegment_087_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 546 30 31, g32p_row21_traceSegment_087_0546_0030, g32p_row21_traceSegment_087_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_087 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 486 60 61, g32p_row21_traceSegment_087_0486_0060, g32p_row21_traceSegment_087_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 607 15 15, g32p_row21_traceSegment_087_0607_0015, g32p_row21_traceSegment_087_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 637 15 16, g32p_row21_traceSegment_087_0637_0015, g32p_row21_traceSegment_087_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 607 30 31, g32p_row21_traceSegment_087_0607_0030, g32p_row21_traceSegment_087_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 668 15 15, g32p_row21_traceSegment_087_0668_0015, g32p_row21_traceSegment_087_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 698 15 16, g32p_row21_traceSegment_087_0698_0015, g32p_row21_traceSegment_087_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 668 30 31, g32p_row21_traceSegment_087_0668_0030, g32p_row21_traceSegment_087_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_087 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 607 61 61, g32p_row21_traceSegment_087_0607_0061, g32p_row21_traceSegment_087_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_087 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 486 121 122, g32p_row21_traceSegment_087_0486_0121, g32p_row21_traceSegment_087_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 729 15 15, g32p_row21_traceSegment_087_0729_0015, g32p_row21_traceSegment_087_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 759 15 15, g32p_row21_traceSegment_087_0759_0015, g32p_row21_traceSegment_087_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_087 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 729 30 30, g32p_row21_traceSegment_087_0729_0030, g32p_row21_traceSegment_087_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 789 15 15, g32p_row21_traceSegment_087_0789_0015, g32p_row21_traceSegment_087_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 819 15 16, g32p_row21_traceSegment_087_0819_0015, g32p_row21_traceSegment_087_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 789 30 31, g32p_row21_traceSegment_087_0789_0030, g32p_row21_traceSegment_087_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_087 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 729 60 61, g32p_row21_traceSegment_087_0729_0060, g32p_row21_traceSegment_087_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 850 15 15, g32p_row21_traceSegment_087_0850_0015, g32p_row21_traceSegment_087_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 880 15 16, g32p_row21_traceSegment_087_0880_0015, g32p_row21_traceSegment_087_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 850 30 31, g32p_row21_traceSegment_087_0850_0030, g32p_row21_traceSegment_087_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_087 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 911 15 15, g32p_row21_traceSegment_087_0911_0015, g32p_row21_traceSegment_087_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_087 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_087 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_087_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_087 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 941 15 16, g32p_row21_traceSegment_087_0941_0015, g32p_row21_traceSegment_087_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_087 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 911 30 31, g32p_row21_traceSegment_087_0911_0030, g32p_row21_traceSegment_087_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_087 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 850 61 61, g32p_row21_traceSegment_087_0850_0061, g32p_row21_traceSegment_087_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_087 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 729 121 122, g32p_row21_traceSegment_087_0729_0121, g32p_row21_traceSegment_087_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_087 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 486 243 243, g32p_row21_traceSegment_087_0486_0243, g32p_row21_traceSegment_087_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_087_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_087 0 972 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_087 0 486 486, g32p_row21_traceSegment_087_0000_0486, g32p_row21_traceSegment_087_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 87 = [3, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_087_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_088 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 88 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_088_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 0 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 0 30 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 0 15 15, g32p_row21_traceSegment_088_0000_0015, g32p_row21_traceSegment_088_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 30 15 15, g32p_row21_traceSegment_088_0030_0015, g32p_row21_traceSegment_088_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_088 0 60 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 0 30 30, g32p_row21_traceSegment_088_0000_0030, g32p_row21_traceSegment_088_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 60 15 15, g32p_row21_traceSegment_088_0060_0015, g32p_row21_traceSegment_088_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 90 15 16, g32p_row21_traceSegment_088_0090_0015, g32p_row21_traceSegment_088_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 60 30 31, g32p_row21_traceSegment_088_0060_0030, g32p_row21_traceSegment_088_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_088 0 121 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 0 60 61, g32p_row21_traceSegment_088_0000_0060, g32p_row21_traceSegment_088_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 121 15 15, g32p_row21_traceSegment_088_0121_0015, g32p_row21_traceSegment_088_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 151 15 16, g32p_row21_traceSegment_088_0151_0015, g32p_row21_traceSegment_088_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 121 30 31, g32p_row21_traceSegment_088_0121_0030, g32p_row21_traceSegment_088_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 182 15 15, g32p_row21_traceSegment_088_0182_0015, g32p_row21_traceSegment_088_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 212 15 16, g32p_row21_traceSegment_088_0212_0015, g32p_row21_traceSegment_088_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 182 30 31, g32p_row21_traceSegment_088_0182_0030, g32p_row21_traceSegment_088_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_088 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 121 61 61, g32p_row21_traceSegment_088_0121_0061, g32p_row21_traceSegment_088_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_088 0 243 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 0 121 122, g32p_row21_traceSegment_088_0000_0121, g32p_row21_traceSegment_088_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 243 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 258 15 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 243 30 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 243 15 15, g32p_row21_traceSegment_088_0243_0015, g32p_row21_traceSegment_088_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 273 15 15, g32p_row21_traceSegment_088_0273_0015, g32p_row21_traceSegment_088_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_088 243 60 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 243 30 30, g32p_row21_traceSegment_088_0243_0030, g32p_row21_traceSegment_088_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 303 15 15, g32p_row21_traceSegment_088_0303_0015, g32p_row21_traceSegment_088_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 333 15 16, g32p_row21_traceSegment_088_0333_0015, g32p_row21_traceSegment_088_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 303 30 31, g32p_row21_traceSegment_088_0303_0030, g32p_row21_traceSegment_088_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_088 243 121 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 243 60 61, g32p_row21_traceSegment_088_0243_0060, g32p_row21_traceSegment_088_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 364 15 15, g32p_row21_traceSegment_088_0364_0015, g32p_row21_traceSegment_088_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 394 15 16, g32p_row21_traceSegment_088_0394_0015, g32p_row21_traceSegment_088_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 364 30 31, g32p_row21_traceSegment_088_0364_0030, g32p_row21_traceSegment_088_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 425 15 15, g32p_row21_traceSegment_088_0425_0015, g32p_row21_traceSegment_088_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 455 15 16, g32p_row21_traceSegment_088_0455_0015, g32p_row21_traceSegment_088_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 425 30 31, g32p_row21_traceSegment_088_0425_0030, g32p_row21_traceSegment_088_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_088 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 364 61 61, g32p_row21_traceSegment_088_0364_0061, g32p_row21_traceSegment_088_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_088 243 243 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 243 121 122, g32p_row21_traceSegment_088_0243_0121, g32p_row21_traceSegment_088_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_088 0 486 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 0 243 243, g32p_row21_traceSegment_088_0000_0243, g32p_row21_traceSegment_088_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 486 15 15, g32p_row21_traceSegment_088_0486_0015, g32p_row21_traceSegment_088_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 516 15 15, g32p_row21_traceSegment_088_0516_0015, g32p_row21_traceSegment_088_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_088 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 486 30 30, g32p_row21_traceSegment_088_0486_0030, g32p_row21_traceSegment_088_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 546 15 15, g32p_row21_traceSegment_088_0546_0015, g32p_row21_traceSegment_088_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 576 15 16, g32p_row21_traceSegment_088_0576_0015, g32p_row21_traceSegment_088_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 546 30 31, g32p_row21_traceSegment_088_0546_0030, g32p_row21_traceSegment_088_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_088 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 486 60 61, g32p_row21_traceSegment_088_0486_0060, g32p_row21_traceSegment_088_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 607 15 15, g32p_row21_traceSegment_088_0607_0015, g32p_row21_traceSegment_088_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 637 15 16, g32p_row21_traceSegment_088_0637_0015, g32p_row21_traceSegment_088_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 607 30 31, g32p_row21_traceSegment_088_0607_0030, g32p_row21_traceSegment_088_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 668 15 15, g32p_row21_traceSegment_088_0668_0015, g32p_row21_traceSegment_088_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 698 15 16, g32p_row21_traceSegment_088_0698_0015, g32p_row21_traceSegment_088_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 668 30 31, g32p_row21_traceSegment_088_0668_0030, g32p_row21_traceSegment_088_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_088 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 607 61 61, g32p_row21_traceSegment_088_0607_0061, g32p_row21_traceSegment_088_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_088 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 486 121 122, g32p_row21_traceSegment_088_0486_0121, g32p_row21_traceSegment_088_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 729 15 15, g32p_row21_traceSegment_088_0729_0015, g32p_row21_traceSegment_088_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 759 15 15, g32p_row21_traceSegment_088_0759_0015, g32p_row21_traceSegment_088_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_088 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 729 30 30, g32p_row21_traceSegment_088_0729_0030, g32p_row21_traceSegment_088_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 789 15 15, g32p_row21_traceSegment_088_0789_0015, g32p_row21_traceSegment_088_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 819 15 16, g32p_row21_traceSegment_088_0819_0015, g32p_row21_traceSegment_088_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 789 30 31, g32p_row21_traceSegment_088_0789_0030, g32p_row21_traceSegment_088_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_088 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 729 60 61, g32p_row21_traceSegment_088_0729_0060, g32p_row21_traceSegment_088_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 850 15 15, g32p_row21_traceSegment_088_0850_0015, g32p_row21_traceSegment_088_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 880 15 16, g32p_row21_traceSegment_088_0880_0015, g32p_row21_traceSegment_088_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 850 30 31, g32p_row21_traceSegment_088_0850_0030, g32p_row21_traceSegment_088_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_088 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 911 15 15, g32p_row21_traceSegment_088_0911_0015, g32p_row21_traceSegment_088_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_088 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_088 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_088_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_088 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 941 15 16, g32p_row21_traceSegment_088_0941_0015, g32p_row21_traceSegment_088_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_088 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 911 30 31, g32p_row21_traceSegment_088_0911_0030, g32p_row21_traceSegment_088_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_088 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 850 61 61, g32p_row21_traceSegment_088_0850_0061, g32p_row21_traceSegment_088_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_088 729 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 729 121 122, g32p_row21_traceSegment_088_0729_0121, g32p_row21_traceSegment_088_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_088 486 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 486 243 243, g32p_row21_traceSegment_088_0486_0243, g32p_row21_traceSegment_088_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_088_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_088 0 972 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_088 0 486 486, g32p_row21_traceSegment_088_0000_0486, g32p_row21_traceSegment_088_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 88 = [3, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_088_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_089 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 89 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_089_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 0 15 15, g32p_row21_traceSegment_089_0000_0015, g32p_row21_traceSegment_089_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 30 15 15, g32p_row21_traceSegment_089_0030_0015, g32p_row21_traceSegment_089_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_089 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 0 30 30, g32p_row21_traceSegment_089_0000_0030, g32p_row21_traceSegment_089_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 60 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 60 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 60 15 15, g32p_row21_traceSegment_089_0060_0015, g32p_row21_traceSegment_089_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 90 15 16, g32p_row21_traceSegment_089_0090_0015, g32p_row21_traceSegment_089_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 60 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 60 30 31, g32p_row21_traceSegment_089_0060_0030, g32p_row21_traceSegment_089_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_089 0 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 0 60 61, g32p_row21_traceSegment_089_0000_0060, g32p_row21_traceSegment_089_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 121 15 15, g32p_row21_traceSegment_089_0121_0015, g32p_row21_traceSegment_089_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 151 15 16, g32p_row21_traceSegment_089_0151_0015, g32p_row21_traceSegment_089_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 121 30 31, g32p_row21_traceSegment_089_0121_0030, g32p_row21_traceSegment_089_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 182 15 15, g32p_row21_traceSegment_089_0182_0015, g32p_row21_traceSegment_089_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 212 15 16, g32p_row21_traceSegment_089_0212_0015, g32p_row21_traceSegment_089_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 182 30 31, g32p_row21_traceSegment_089_0182_0030, g32p_row21_traceSegment_089_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_089 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 121 61 61, g32p_row21_traceSegment_089_0121_0061, g32p_row21_traceSegment_089_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_089 0 243 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 0 121 122, g32p_row21_traceSegment_089_0000_0121, g32p_row21_traceSegment_089_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 243 15 15, g32p_row21_traceSegment_089_0243_0015, g32p_row21_traceSegment_089_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 288 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 273 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 273 15 15, g32p_row21_traceSegment_089_0273_0015, g32p_row21_traceSegment_089_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_089 243 60 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 243 30 30, g32p_row21_traceSegment_089_0243_0030, g32p_row21_traceSegment_089_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 303 15 15, g32p_row21_traceSegment_089_0303_0015, g32p_row21_traceSegment_089_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 333 15 16, g32p_row21_traceSegment_089_0333_0015, g32p_row21_traceSegment_089_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 303 30 31, g32p_row21_traceSegment_089_0303_0030, g32p_row21_traceSegment_089_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_089 243 121 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 243 60 61, g32p_row21_traceSegment_089_0243_0060, g32p_row21_traceSegment_089_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 364 15 15, g32p_row21_traceSegment_089_0364_0015, g32p_row21_traceSegment_089_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 409 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 394 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 394 15 16, g32p_row21_traceSegment_089_0394_0015, g32p_row21_traceSegment_089_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 364 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 364 30 31, g32p_row21_traceSegment_089_0364_0030, g32p_row21_traceSegment_089_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 425 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 425 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 425 15 15, g32p_row21_traceSegment_089_0425_0015, g32p_row21_traceSegment_089_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 455 15 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 455 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 455 15 16, g32p_row21_traceSegment_089_0455_0015, g32p_row21_traceSegment_089_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 425 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 425 30 31, g32p_row21_traceSegment_089_0425_0030, g32p_row21_traceSegment_089_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_089 364 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 364 61 61, g32p_row21_traceSegment_089_0364_0061, g32p_row21_traceSegment_089_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_089 243 243 = [0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 243 121 122, g32p_row21_traceSegment_089_0243_0121, g32p_row21_traceSegment_089_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_089 0 486 = [0, 1, 6] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 0 243 243, g32p_row21_traceSegment_089_0000_0243, g32p_row21_traceSegment_089_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 501 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 486 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 486 15 15, g32p_row21_traceSegment_089_0486_0015, g32p_row21_traceSegment_089_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 516 15 15, g32p_row21_traceSegment_089_0516_0015, g32p_row21_traceSegment_089_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_089 486 60 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 486 30 30, g32p_row21_traceSegment_089_0486_0030, g32p_row21_traceSegment_089_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 561 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 546 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 546 15 15, g32p_row21_traceSegment_089_0546_0015, g32p_row21_traceSegment_089_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 591 16 = [0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 576 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 576 15 16, g32p_row21_traceSegment_089_0576_0015, g32p_row21_traceSegment_089_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 546 61 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 546 30 31, g32p_row21_traceSegment_089_0546_0030, g32p_row21_traceSegment_089_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_089 486 121 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 486 60 61, g32p_row21_traceSegment_089_0486_0060, g32p_row21_traceSegment_089_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 607 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 622 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 607 30 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 607 15 15, g32p_row21_traceSegment_089_0607_0015, g32p_row21_traceSegment_089_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 637 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 652 16 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 637 31 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 637 15 16, g32p_row21_traceSegment_089_0637_0015, g32p_row21_traceSegment_089_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 607 61 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 607 30 31, g32p_row21_traceSegment_089_0607_0030, g32p_row21_traceSegment_089_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 668 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 668 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 668 15 15, g32p_row21_traceSegment_089_0668_0015, g32p_row21_traceSegment_089_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 698 15 16, g32p_row21_traceSegment_089_0698_0015, g32p_row21_traceSegment_089_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 668 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 668 30 31, g32p_row21_traceSegment_089_0668_0030, g32p_row21_traceSegment_089_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_089 607 122 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 607 61 61, g32p_row21_traceSegment_089_0607_0061, g32p_row21_traceSegment_089_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_089 486 243 = [0, 7, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 486 121 122, g32p_row21_traceSegment_089_0486_0121, g32p_row21_traceSegment_089_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 729 15 15, g32p_row21_traceSegment_089_0729_0015, g32p_row21_traceSegment_089_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 759 15 15, g32p_row21_traceSegment_089_0759_0015, g32p_row21_traceSegment_089_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_089 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 729 30 30, g32p_row21_traceSegment_089_0729_0030, g32p_row21_traceSegment_089_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 789 15 15, g32p_row21_traceSegment_089_0789_0015, g32p_row21_traceSegment_089_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 819 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 819 15 16, g32p_row21_traceSegment_089_0819_0015, g32p_row21_traceSegment_089_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 789 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 789 30 31, g32p_row21_traceSegment_089_0789_0030, g32p_row21_traceSegment_089_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_089 729 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 729 60 61, g32p_row21_traceSegment_089_0729_0060, g32p_row21_traceSegment_089_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 850 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 850 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 850 15 15, g32p_row21_traceSegment_089_0850_0015, g32p_row21_traceSegment_089_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 880 15 16, g32p_row21_traceSegment_089_0880_0015, g32p_row21_traceSegment_089_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 850 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 850 30 31, g32p_row21_traceSegment_089_0850_0030, g32p_row21_traceSegment_089_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 911 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_089 911 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 911 15 15, g32p_row21_traceSegment_089_0911_0015, g32p_row21_traceSegment_089_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_089 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_089 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_089_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_089 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 941 15 16, g32p_row21_traceSegment_089_0941_0015, g32p_row21_traceSegment_089_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_089 911 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 911 30 31, g32p_row21_traceSegment_089_0911_0030, g32p_row21_traceSegment_089_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_089 850 122 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 850 61 61, g32p_row21_traceSegment_089_0850_0061, g32p_row21_traceSegment_089_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_089 729 243 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 729 121 122, g32p_row21_traceSegment_089_0729_0121, g32p_row21_traceSegment_089_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_089 486 486 = [0, 8, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 486 243 243, g32p_row21_traceSegment_089_0486_0243, g32p_row21_traceSegment_089_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_089_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_089 0 972 = [0, 9, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_089 0 486 486, g32p_row21_traceSegment_089_0000_0486, g32p_row21_traceSegment_089_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 89 = [0, 9, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_089_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_091 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 91 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_091_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 0 15 15, g32p_row21_traceSegment_091_0000_0015, g32p_row21_traceSegment_091_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 30 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 45 15 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 30 30 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 30 15 15, g32p_row21_traceSegment_091_0030_0015, g32p_row21_traceSegment_091_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_091 0 60 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 0 30 30, g32p_row21_traceSegment_091_0000_0030, g32p_row21_traceSegment_091_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 60 15 15, g32p_row21_traceSegment_091_0060_0015, g32p_row21_traceSegment_091_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 90 15 16, g32p_row21_traceSegment_091_0090_0015, g32p_row21_traceSegment_091_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 60 30 31, g32p_row21_traceSegment_091_0060_0030, g32p_row21_traceSegment_091_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_091 0 121 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 0 60 61, g32p_row21_traceSegment_091_0000_0060, g32p_row21_traceSegment_091_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 121 15 15, g32p_row21_traceSegment_091_0121_0015, g32p_row21_traceSegment_091_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 166 16 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 151 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 151 15 16, g32p_row21_traceSegment_091_0151_0015, g32p_row21_traceSegment_091_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 121 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 121 30 31, g32p_row21_traceSegment_091_0121_0030, g32p_row21_traceSegment_091_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 182 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 182 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 182 15 15, g32p_row21_traceSegment_091_0182_0015, g32p_row21_traceSegment_091_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 212 15 16, g32p_row21_traceSegment_091_0212_0015, g32p_row21_traceSegment_091_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 182 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 182 30 31, g32p_row21_traceSegment_091_0182_0030, g32p_row21_traceSegment_091_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_091 121 122 = [4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 121 61 61, g32p_row21_traceSegment_091_0121_0061, g32p_row21_traceSegment_091_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_091 0 243 = [5, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 0 121 122, g32p_row21_traceSegment_091_0000_0121, g32p_row21_traceSegment_091_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 243 15 15, g32p_row21_traceSegment_091_0243_0015, g32p_row21_traceSegment_091_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 273 15 15, g32p_row21_traceSegment_091_0273_0015, g32p_row21_traceSegment_091_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_091 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 243 30 30, g32p_row21_traceSegment_091_0243_0030, g32p_row21_traceSegment_091_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 303 15 15, g32p_row21_traceSegment_091_0303_0015, g32p_row21_traceSegment_091_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 333 15 16, g32p_row21_traceSegment_091_0333_0015, g32p_row21_traceSegment_091_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 303 30 31, g32p_row21_traceSegment_091_0303_0030, g32p_row21_traceSegment_091_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_091 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 243 60 61, g32p_row21_traceSegment_091_0243_0060, g32p_row21_traceSegment_091_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 364 15 15, g32p_row21_traceSegment_091_0364_0015, g32p_row21_traceSegment_091_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 409 16 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 394 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 394 15 16, g32p_row21_traceSegment_091_0394_0015, g32p_row21_traceSegment_091_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 364 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 364 30 31, g32p_row21_traceSegment_091_0364_0030, g32p_row21_traceSegment_091_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 425 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 440 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 425 30 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 425 15 15, g32p_row21_traceSegment_091_0425_0015, g32p_row21_traceSegment_091_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 455 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 455 31 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 455 15 16, g32p_row21_traceSegment_091_0455_0015, g32p_row21_traceSegment_091_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 425 61 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 425 30 31, g32p_row21_traceSegment_091_0425_0030, g32p_row21_traceSegment_091_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_091 364 122 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 364 61 61, g32p_row21_traceSegment_091_0364_0061, g32p_row21_traceSegment_091_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_091 243 243 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 243 121 122, g32p_row21_traceSegment_091_0243_0121, g32p_row21_traceSegment_091_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_091 0 486 = [5, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 0 243 243, g32p_row21_traceSegment_091_0000_0243, g32p_row21_traceSegment_091_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 486 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 486 30 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 486 15 15, g32p_row21_traceSegment_091_0486_0015, g32p_row21_traceSegment_091_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 516 15 15, g32p_row21_traceSegment_091_0516_0015, g32p_row21_traceSegment_091_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_091 486 60 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 486 30 30, g32p_row21_traceSegment_091_0486_0030, g32p_row21_traceSegment_091_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 546 15 15, g32p_row21_traceSegment_091_0546_0015, g32p_row21_traceSegment_091_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 576 15 16, g32p_row21_traceSegment_091_0576_0015, g32p_row21_traceSegment_091_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 546 30 31, g32p_row21_traceSegment_091_0546_0030, g32p_row21_traceSegment_091_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_091 486 121 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 486 60 61, g32p_row21_traceSegment_091_0486_0060, g32p_row21_traceSegment_091_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 607 15 15, g32p_row21_traceSegment_091_0607_0015, g32p_row21_traceSegment_091_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 637 15 16, g32p_row21_traceSegment_091_0637_0015, g32p_row21_traceSegment_091_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 607 30 31, g32p_row21_traceSegment_091_0607_0030, g32p_row21_traceSegment_091_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 668 15 15, g32p_row21_traceSegment_091_0668_0015, g32p_row21_traceSegment_091_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 698 15 16, g32p_row21_traceSegment_091_0698_0015, g32p_row21_traceSegment_091_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 668 30 31, g32p_row21_traceSegment_091_0668_0030, g32p_row21_traceSegment_091_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_091 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 607 61 61, g32p_row21_traceSegment_091_0607_0061, g32p_row21_traceSegment_091_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_091 486 243 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 486 121 122, g32p_row21_traceSegment_091_0486_0121, g32p_row21_traceSegment_091_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 729 15 15, g32p_row21_traceSegment_091_0729_0015, g32p_row21_traceSegment_091_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 759 15 15, g32p_row21_traceSegment_091_0759_0015, g32p_row21_traceSegment_091_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_091 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 729 30 30, g32p_row21_traceSegment_091_0729_0030, g32p_row21_traceSegment_091_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 804 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 789 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 789 15 15, g32p_row21_traceSegment_091_0789_0015, g32p_row21_traceSegment_091_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 819 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 834 16 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 819 31 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 819 15 16, g32p_row21_traceSegment_091_0819_0015, g32p_row21_traceSegment_091_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 789 61 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 789 30 31, g32p_row21_traceSegment_091_0789_0030, g32p_row21_traceSegment_091_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_091 729 121 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 729 60 61, g32p_row21_traceSegment_091_0729_0060, g32p_row21_traceSegment_091_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 850 15 15, g32p_row21_traceSegment_091_0850_0015, g32p_row21_traceSegment_091_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 880 15 = [2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 880 31 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 880 15 16, g32p_row21_traceSegment_091_0880_0015, g32p_row21_traceSegment_091_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 850 61 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 850 30 31, g32p_row21_traceSegment_091_0850_0030, g32p_row21_traceSegment_091_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_091 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 911 15 15, g32p_row21_traceSegment_091_0911_0015, g32p_row21_traceSegment_091_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_091 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_091 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_091_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_091 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 941 15 16, g32p_row21_traceSegment_091_0941_0015, g32p_row21_traceSegment_091_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_091 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 911 30 31, g32p_row21_traceSegment_091_0911_0030, g32p_row21_traceSegment_091_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_091 850 122 = [2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 850 61 61, g32p_row21_traceSegment_091_0850_0061, g32p_row21_traceSegment_091_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_091 729 243 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 729 121 122, g32p_row21_traceSegment_091_0729_0121, g32p_row21_traceSegment_091_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_091 486 486 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 486 243 243, g32p_row21_traceSegment_091_0486_0243, g32p_row21_traceSegment_091_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_091_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_091 0 972 = [9, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_091 0 486 486, g32p_row21_traceSegment_091_0000_0486, g32p_row21_traceSegment_091_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 91 = [9, 0, 9] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_091_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_092 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 92 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_092_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 0 15 15, g32p_row21_traceSegment_092_0000_0015, g32p_row21_traceSegment_092_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 30 15 15, g32p_row21_traceSegment_092_0030_0015, g32p_row21_traceSegment_092_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_092 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 0 30 30, g32p_row21_traceSegment_092_0000_0030, g32p_row21_traceSegment_092_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 60 15 15, g32p_row21_traceSegment_092_0060_0015, g32p_row21_traceSegment_092_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 90 15 16, g32p_row21_traceSegment_092_0090_0015, g32p_row21_traceSegment_092_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 60 30 31, g32p_row21_traceSegment_092_0060_0030, g32p_row21_traceSegment_092_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_092 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 0 60 61, g32p_row21_traceSegment_092_0000_0060, g32p_row21_traceSegment_092_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 136 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 121 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 121 15 15, g32p_row21_traceSegment_092_0121_0015, g32p_row21_traceSegment_092_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 151 15 16, g32p_row21_traceSegment_092_0151_0015, g32p_row21_traceSegment_092_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 121 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 121 30 31, g32p_row21_traceSegment_092_0121_0030, g32p_row21_traceSegment_092_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 182 15 15, g32p_row21_traceSegment_092_0182_0015, g32p_row21_traceSegment_092_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 212 15 16, g32p_row21_traceSegment_092_0212_0015, g32p_row21_traceSegment_092_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 182 30 31, g32p_row21_traceSegment_092_0182_0030, g32p_row21_traceSegment_092_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_092 121 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 121 61 61, g32p_row21_traceSegment_092_0121_0061, g32p_row21_traceSegment_092_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_092 0 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 0 121 122, g32p_row21_traceSegment_092_0000_0121, g32p_row21_traceSegment_092_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 243 15 15, g32p_row21_traceSegment_092_0243_0015, g32p_row21_traceSegment_092_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 273 15 15, g32p_row21_traceSegment_092_0273_0015, g32p_row21_traceSegment_092_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_092 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 243 30 30, g32p_row21_traceSegment_092_0243_0030, g32p_row21_traceSegment_092_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 303 15 15, g32p_row21_traceSegment_092_0303_0015, g32p_row21_traceSegment_092_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 333 15 16, g32p_row21_traceSegment_092_0333_0015, g32p_row21_traceSegment_092_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 303 30 31, g32p_row21_traceSegment_092_0303_0030, g32p_row21_traceSegment_092_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_092 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 243 60 61, g32p_row21_traceSegment_092_0243_0060, g32p_row21_traceSegment_092_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 364 15 15, g32p_row21_traceSegment_092_0364_0015, g32p_row21_traceSegment_092_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 394 15 16, g32p_row21_traceSegment_092_0394_0015, g32p_row21_traceSegment_092_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 364 30 31, g32p_row21_traceSegment_092_0364_0030, g32p_row21_traceSegment_092_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 425 15 15, g32p_row21_traceSegment_092_0425_0015, g32p_row21_traceSegment_092_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 455 15 16, g32p_row21_traceSegment_092_0455_0015, g32p_row21_traceSegment_092_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 425 30 31, g32p_row21_traceSegment_092_0425_0030, g32p_row21_traceSegment_092_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_092 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 364 61 61, g32p_row21_traceSegment_092_0364_0061, g32p_row21_traceSegment_092_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_092 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 243 121 122, g32p_row21_traceSegment_092_0243_0121, g32p_row21_traceSegment_092_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_092 0 486 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 0 243 243, g32p_row21_traceSegment_092_0000_0243, g32p_row21_traceSegment_092_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 486 15 15, g32p_row21_traceSegment_092_0486_0015, g32p_row21_traceSegment_092_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 516 15 15, g32p_row21_traceSegment_092_0516_0015, g32p_row21_traceSegment_092_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_092 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 486 30 30, g32p_row21_traceSegment_092_0486_0030, g32p_row21_traceSegment_092_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 546 15 15, g32p_row21_traceSegment_092_0546_0015, g32p_row21_traceSegment_092_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 576 15 16, g32p_row21_traceSegment_092_0576_0015, g32p_row21_traceSegment_092_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 546 30 31, g32p_row21_traceSegment_092_0546_0030, g32p_row21_traceSegment_092_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_092 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 486 60 61, g32p_row21_traceSegment_092_0486_0060, g32p_row21_traceSegment_092_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 607 15 15, g32p_row21_traceSegment_092_0607_0015, g32p_row21_traceSegment_092_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 637 15 16, g32p_row21_traceSegment_092_0637_0015, g32p_row21_traceSegment_092_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 607 30 31, g32p_row21_traceSegment_092_0607_0030, g32p_row21_traceSegment_092_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 668 15 15, g32p_row21_traceSegment_092_0668_0015, g32p_row21_traceSegment_092_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 698 15 16, g32p_row21_traceSegment_092_0698_0015, g32p_row21_traceSegment_092_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 668 30 31, g32p_row21_traceSegment_092_0668_0030, g32p_row21_traceSegment_092_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_092 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 607 61 61, g32p_row21_traceSegment_092_0607_0061, g32p_row21_traceSegment_092_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_092 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 486 121 122, g32p_row21_traceSegment_092_0486_0121, g32p_row21_traceSegment_092_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 729 15 15, g32p_row21_traceSegment_092_0729_0015, g32p_row21_traceSegment_092_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 759 15 15, g32p_row21_traceSegment_092_0759_0015, g32p_row21_traceSegment_092_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_092 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 729 30 30, g32p_row21_traceSegment_092_0729_0030, g32p_row21_traceSegment_092_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 789 15 = [1, 2] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 804 15 = [1, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 789 30 = [2, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 789 15 15, g32p_row21_traceSegment_092_0789_0015, g32p_row21_traceSegment_092_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 819 15 = [1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 819 31 = [1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 819 15 16, g32p_row21_traceSegment_092_0819_0015, g32p_row21_traceSegment_092_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 789 61 = [3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 789 30 31, g32p_row21_traceSegment_092_0789_0030, g32p_row21_traceSegment_092_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_092 729 121 = [3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 729 60 61, g32p_row21_traceSegment_092_0729_0060, g32p_row21_traceSegment_092_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 850 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 850 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 850 15 15, g32p_row21_traceSegment_092_0850_0015, g32p_row21_traceSegment_092_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 880 15 16, g32p_row21_traceSegment_092_0880_0015, g32p_row21_traceSegment_092_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 850 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 850 30 31, g32p_row21_traceSegment_092_0850_0030, g32p_row21_traceSegment_092_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_092 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 911 15 15, g32p_row21_traceSegment_092_0911_0015, g32p_row21_traceSegment_092_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_092 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_092 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_092_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_092 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 941 15 16, g32p_row21_traceSegment_092_0941_0015, g32p_row21_traceSegment_092_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_092 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 911 30 31, g32p_row21_traceSegment_092_0911_0030, g32p_row21_traceSegment_092_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_092 850 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 850 61 61, g32p_row21_traceSegment_092_0850_0061, g32p_row21_traceSegment_092_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_092 729 243 = [3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 729 121 122, g32p_row21_traceSegment_092_0729_0121, g32p_row21_traceSegment_092_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_092 486 486 = [3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 486 243 243, g32p_row21_traceSegment_092_0486_0243, g32p_row21_traceSegment_092_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_092_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_092 0 972 = [3, 3] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_092 0 486 486, g32p_row21_traceSegment_092_0000_0486, g32p_row21_traceSegment_092_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 92 = [3, 3] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_092_0000_0972

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row21_traceSegment_093 (k : ℕ) : List ℤ :=
  if g32p_row21_supplierClassifier (Fin.ofNat 972 k) = 93 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row21_characterValues (Fin.ofNat 972 k))).val 1 else []

private theorem g32p_row21_traceSegment_093_0000_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 0 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0015_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 15 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0000_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 0 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 0 15 15, g32p_row21_traceSegment_093_0000_0015, g32p_row21_traceSegment_093_0015_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0030_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 30 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0045_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 45 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0030_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 30 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 30 15 15, g32p_row21_traceSegment_093_0030_0015, g32p_row21_traceSegment_093_0045_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0000_0060 : g32p_coeffSegment g32p_row21_traceSegment_093 0 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 0 30 30, g32p_row21_traceSegment_093_0000_0030, g32p_row21_traceSegment_093_0030_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0060_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 60 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0075_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 75 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0060_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 60 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 60 15 15, g32p_row21_traceSegment_093_0060_0015, g32p_row21_traceSegment_093_0075_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0090_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 90 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0105_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 105 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0090_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 90 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 90 15 16, g32p_row21_traceSegment_093_0090_0015, g32p_row21_traceSegment_093_0105_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0060_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 60 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 60 30 31, g32p_row21_traceSegment_093_0060_0030, g32p_row21_traceSegment_093_0090_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0000_0121 : g32p_coeffSegment g32p_row21_traceSegment_093 0 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 0 60 61, g32p_row21_traceSegment_093_0000_0060, g32p_row21_traceSegment_093_0060_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0121_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 121 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0136_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 136 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0121_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 121 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 121 15 15, g32p_row21_traceSegment_093_0121_0015, g32p_row21_traceSegment_093_0136_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0151_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 151 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0166_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 166 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0151_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 151 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 151 15 16, g32p_row21_traceSegment_093_0151_0015, g32p_row21_traceSegment_093_0166_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0121_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 121 61 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 121 30 31, g32p_row21_traceSegment_093_0121_0030, g32p_row21_traceSegment_093_0151_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0182_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 182 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0197_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 197 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0182_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 182 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 182 15 15, g32p_row21_traceSegment_093_0182_0015, g32p_row21_traceSegment_093_0197_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0212_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 212 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0227_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 227 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0212_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 212 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 212 15 16, g32p_row21_traceSegment_093_0212_0015, g32p_row21_traceSegment_093_0227_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0182_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 182 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 182 30 31, g32p_row21_traceSegment_093_0182_0030, g32p_row21_traceSegment_093_0212_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0121_0122 : g32p_coeffSegment g32p_row21_traceSegment_093 121 122 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 121 61 61, g32p_row21_traceSegment_093_0121_0061, g32p_row21_traceSegment_093_0182_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0000_0243 : g32p_coeffSegment g32p_row21_traceSegment_093 0 243 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 0 121 122, g32p_row21_traceSegment_093_0000_0121, g32p_row21_traceSegment_093_0121_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0243_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 243 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0258_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 258 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0243_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 243 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 243 15 15, g32p_row21_traceSegment_093_0243_0015, g32p_row21_traceSegment_093_0258_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0273_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 273 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0288_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 288 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0273_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 273 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 273 15 15, g32p_row21_traceSegment_093_0273_0015, g32p_row21_traceSegment_093_0288_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0243_0060 : g32p_coeffSegment g32p_row21_traceSegment_093 243 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 243 30 30, g32p_row21_traceSegment_093_0243_0030, g32p_row21_traceSegment_093_0273_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0303_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 303 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0318_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 318 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0303_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 303 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 303 15 15, g32p_row21_traceSegment_093_0303_0015, g32p_row21_traceSegment_093_0318_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0333_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 333 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0348_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 348 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0333_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 333 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 333 15 16, g32p_row21_traceSegment_093_0333_0015, g32p_row21_traceSegment_093_0348_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0303_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 303 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 303 30 31, g32p_row21_traceSegment_093_0303_0030, g32p_row21_traceSegment_093_0333_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0243_0121 : g32p_coeffSegment g32p_row21_traceSegment_093 243 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 243 60 61, g32p_row21_traceSegment_093_0243_0060, g32p_row21_traceSegment_093_0303_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0364_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 364 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0379_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 379 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0364_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 364 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 364 15 15, g32p_row21_traceSegment_093_0364_0015, g32p_row21_traceSegment_093_0379_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0394_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 394 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0409_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 409 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0394_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 394 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 394 15 16, g32p_row21_traceSegment_093_0394_0015, g32p_row21_traceSegment_093_0409_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0364_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 364 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 364 30 31, g32p_row21_traceSegment_093_0364_0030, g32p_row21_traceSegment_093_0394_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0425_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 425 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0440_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 440 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0425_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 425 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 425 15 15, g32p_row21_traceSegment_093_0425_0015, g32p_row21_traceSegment_093_0440_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0455_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 455 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0470_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 470 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0455_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 455 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 455 15 16, g32p_row21_traceSegment_093_0455_0015, g32p_row21_traceSegment_093_0470_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0425_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 425 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 425 30 31, g32p_row21_traceSegment_093_0425_0030, g32p_row21_traceSegment_093_0455_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0364_0122 : g32p_coeffSegment g32p_row21_traceSegment_093 364 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 364 61 61, g32p_row21_traceSegment_093_0364_0061, g32p_row21_traceSegment_093_0425_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0243_0243 : g32p_coeffSegment g32p_row21_traceSegment_093 243 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 243 121 122, g32p_row21_traceSegment_093_0243_0121, g32p_row21_traceSegment_093_0364_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0000_0486 : g32p_coeffSegment g32p_row21_traceSegment_093 0 486 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 0 243 243, g32p_row21_traceSegment_093_0000_0243, g32p_row21_traceSegment_093_0243_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0486_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 486 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0501_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 501 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0486_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 486 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 486 15 15, g32p_row21_traceSegment_093_0486_0015, g32p_row21_traceSegment_093_0501_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0516_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 516 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0531_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 531 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0516_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 516 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 516 15 15, g32p_row21_traceSegment_093_0516_0015, g32p_row21_traceSegment_093_0531_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0486_0060 : g32p_coeffSegment g32p_row21_traceSegment_093 486 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 486 30 30, g32p_row21_traceSegment_093_0486_0030, g32p_row21_traceSegment_093_0516_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0546_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 546 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0561_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 561 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0546_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 546 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 546 15 15, g32p_row21_traceSegment_093_0546_0015, g32p_row21_traceSegment_093_0561_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0576_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 576 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0591_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 591 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0576_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 576 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 576 15 16, g32p_row21_traceSegment_093_0576_0015, g32p_row21_traceSegment_093_0591_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0546_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 546 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 546 30 31, g32p_row21_traceSegment_093_0546_0030, g32p_row21_traceSegment_093_0576_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0486_0121 : g32p_coeffSegment g32p_row21_traceSegment_093 486 121 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 486 60 61, g32p_row21_traceSegment_093_0486_0060, g32p_row21_traceSegment_093_0546_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0607_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 607 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0622_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 622 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0607_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 607 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 607 15 15, g32p_row21_traceSegment_093_0607_0015, g32p_row21_traceSegment_093_0622_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0637_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 637 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0652_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 652 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0637_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 637 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 637 15 16, g32p_row21_traceSegment_093_0637_0015, g32p_row21_traceSegment_093_0652_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0607_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 607 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 607 30 31, g32p_row21_traceSegment_093_0607_0030, g32p_row21_traceSegment_093_0637_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0668_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 668 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0683_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 683 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0668_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 668 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 668 15 15, g32p_row21_traceSegment_093_0668_0015, g32p_row21_traceSegment_093_0683_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0698_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 698 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0713_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 713 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0698_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 698 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 698 15 16, g32p_row21_traceSegment_093_0698_0015, g32p_row21_traceSegment_093_0713_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0668_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 668 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 668 30 31, g32p_row21_traceSegment_093_0668_0030, g32p_row21_traceSegment_093_0698_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0607_0122 : g32p_coeffSegment g32p_row21_traceSegment_093 607 122 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 607 61 61, g32p_row21_traceSegment_093_0607_0061, g32p_row21_traceSegment_093_0668_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0486_0243 : g32p_coeffSegment g32p_row21_traceSegment_093 486 243 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 486 121 122, g32p_row21_traceSegment_093_0486_0121, g32p_row21_traceSegment_093_0607_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0729_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 729 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0744_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 744 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0729_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 729 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 729 15 15, g32p_row21_traceSegment_093_0729_0015, g32p_row21_traceSegment_093_0744_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0759_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 759 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0774_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 774 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0759_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 759 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 759 15 15, g32p_row21_traceSegment_093_0759_0015, g32p_row21_traceSegment_093_0774_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0729_0060 : g32p_coeffSegment g32p_row21_traceSegment_093 729 60 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 729 30 30, g32p_row21_traceSegment_093_0729_0030, g32p_row21_traceSegment_093_0759_0030]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0789_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 789 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0804_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 804 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0789_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 789 30 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 789 15 15, g32p_row21_traceSegment_093_0789_0015, g32p_row21_traceSegment_093_0804_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0819_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 819 15 = [0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0834_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 834 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0819_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 819 31 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 819 15 16, g32p_row21_traceSegment_093_0819_0015, g32p_row21_traceSegment_093_0834_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0789_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 789 61 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 789 30 31, g32p_row21_traceSegment_093_0789_0030, g32p_row21_traceSegment_093_0819_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0729_0121 : g32p_coeffSegment g32p_row21_traceSegment_093 729 121 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 729 60 61, g32p_row21_traceSegment_093_0729_0060, g32p_row21_traceSegment_093_0789_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0850_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 850 15 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0865_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 865 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0850_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 850 30 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 850 15 15, g32p_row21_traceSegment_093_0850_0015, g32p_row21_traceSegment_093_0865_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0880_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 880 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0895_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 895 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0880_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 880 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 880 15 16, g32p_row21_traceSegment_093_0880_0015, g32p_row21_traceSegment_093_0895_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0850_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 850 61 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 850 30 31, g32p_row21_traceSegment_093_0850_0030, g32p_row21_traceSegment_093_0880_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0911_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 911 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0926_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 926 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0911_0030 : g32p_coeffSegment g32p_row21_traceSegment_093 911 30 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 911 15 15, g32p_row21_traceSegment_093_0911_0015, g32p_row21_traceSegment_093_0926_0015]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0941_0015 : g32p_coeffSegment g32p_row21_traceSegment_093 941 15 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0956_0016 : g32p_coeffSegment g32p_row21_traceSegment_093 956 16 = [] := by
  decide +kernel

private theorem g32p_row21_traceSegment_093_0941_0031 : g32p_coeffSegment g32p_row21_traceSegment_093 941 31 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 941 15 16, g32p_row21_traceSegment_093_0941_0015, g32p_row21_traceSegment_093_0956_0016]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0911_0061 : g32p_coeffSegment g32p_row21_traceSegment_093 911 61 = [] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 911 30 31, g32p_row21_traceSegment_093_0911_0030, g32p_row21_traceSegment_093_0941_0031]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0850_0122 : g32p_coeffSegment g32p_row21_traceSegment_093 850 122 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 850 61 61, g32p_row21_traceSegment_093_0850_0061, g32p_row21_traceSegment_093_0911_0061]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0729_0243 : g32p_coeffSegment g32p_row21_traceSegment_093 729 243 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 729 121 122, g32p_row21_traceSegment_093_0729_0121, g32p_row21_traceSegment_093_0850_0122]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0486_0486 : g32p_coeffSegment g32p_row21_traceSegment_093 486 486 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 486 243 243, g32p_row21_traceSegment_093_0486_0243, g32p_row21_traceSegment_093_0729_0243]
  decide +kernel

private theorem g32p_row21_traceSegment_093_0000_0972 : g32p_coeffSegment g32p_row21_traceSegment_093 0 972 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row21_traceSegment_093 0 486 486, g32p_row21_traceSegment_093_0000_0486, g32p_row21_traceSegment_093_0486_0486]
  decide +kernel

theorem g32p_row21_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row21_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row21_characterValues j)).val) 93 = [0, 3, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row21_traceSegment_093_0000_0972

end HodgeLean.Foundations.Program

end
end
