import HodgeLean.Foundations.Program.G32PropFourSixPacked0397
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row25_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 0) (g32p_literalTraceValue 24 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row25_traceCoefficients_000]
  decide +kernel

theorem g32p_row25_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 4) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 4) (g32p_literalTraceValue 24 4)
      [1, -1, 1] [5184, 5184, 5184] = true := by
  rw [g32p_row25_traceCoefficients_004]
  decide +kernel

theorem g32p_row25_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 5) (g32p_literalTraceValue 24 5)
      [1, -1, 1] [3456, 3456] = true := by
  rw [g32p_row25_traceCoefficients_005]
  decide +kernel

theorem g32p_row25_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 11) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 11) (g32p_literalTraceValue 24 11)
      [1, -1, 1] [] = true := by
  rw [g32p_row25_traceCoefficients_011]
  decide +kernel

theorem g32p_row25_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 13) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 13) (g32p_literalTraceValue 24 13)
      [1, -1, 1] [0, 0, 3456, 3456] = true := by
  rw [g32p_row25_traceCoefficients_013]
  decide +kernel

theorem g32p_row25_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 18) (g32p_literalTraceValue 24 18)
      [1, -1, 1] [6912, 6912] = true := by
  rw [g32p_row25_traceCoefficients_018]
  decide +kernel

theorem g32p_row25_tracePolynomial_021 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 21) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 21) (g32p_literalTraceValue 24 21)
      [1, -1, 1] [] = true := by
  rw [g32p_row25_traceCoefficients_021]
  decide +kernel

theorem g32p_row25_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 24) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 24) (g32p_literalTraceValue 24 24)
      [1, -1, 1] [] = true := by
  rw [g32p_row25_traceCoefficients_024]
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

private def g32p_row25_traceSegment_025 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 25 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_025_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 0 9 9, g32p_row25_traceSegment_025_0000_0009, g32p_row25_traceSegment_025_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 18 9 9, g32p_row25_traceSegment_025_0018_0009, g32p_row25_traceSegment_025_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 0 18 18, g32p_row25_traceSegment_025_0000_0018, g32p_row25_traceSegment_025_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 36 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 36 9 9, g32p_row25_traceSegment_025_0036_0009, g32p_row25_traceSegment_025_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 54 9 9, g32p_row25_traceSegment_025_0054_0009, g32p_row25_traceSegment_025_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 36 18 18, g32p_row25_traceSegment_025_0036_0018, g32p_row25_traceSegment_025_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_025 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 0 36 36, g32p_row25_traceSegment_025_0000_0036, g32p_row25_traceSegment_025_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 72 9 9, g32p_row25_traceSegment_025_0072_0009, g32p_row25_traceSegment_025_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 90 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 90 9 9, g32p_row25_traceSegment_025_0090_0009, g32p_row25_traceSegment_025_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 72 18 18, g32p_row25_traceSegment_025_0072_0018, g32p_row25_traceSegment_025_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 108 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 108 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 108 9 9, g32p_row25_traceSegment_025_0108_0009, g32p_row25_traceSegment_025_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 126 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 126 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 126 9 9, g32p_row25_traceSegment_025_0126_0009, g32p_row25_traceSegment_025_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 108 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 108 18 18, g32p_row25_traceSegment_025_0108_0018, g32p_row25_traceSegment_025_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_025 72 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 72 36 36, g32p_row25_traceSegment_025_0072_0036, g32p_row25_traceSegment_025_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_025 0 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 0 72 72, g32p_row25_traceSegment_025_0000_0072, g32p_row25_traceSegment_025_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 144 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 153 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 144 9 9, g32p_row25_traceSegment_025_0144_0009, g32p_row25_traceSegment_025_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 162 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 162 9 9, g32p_row25_traceSegment_025_0162_0009, g32p_row25_traceSegment_025_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 144 18 18, g32p_row25_traceSegment_025_0144_0018, g32p_row25_traceSegment_025_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 180 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 189 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 180 9 9, g32p_row25_traceSegment_025_0180_0009, g32p_row25_traceSegment_025_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 198 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 207 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 198 9 9, g32p_row25_traceSegment_025_0198_0009, g32p_row25_traceSegment_025_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 180 18 18, g32p_row25_traceSegment_025_0180_0018, g32p_row25_traceSegment_025_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_025 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 144 36 36, g32p_row25_traceSegment_025_0144_0036, g32p_row25_traceSegment_025_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 216 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 225 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 216 9 9, g32p_row25_traceSegment_025_0216_0009, g32p_row25_traceSegment_025_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 234 9 9, g32p_row25_traceSegment_025_0234_0009, g32p_row25_traceSegment_025_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 216 18 18, g32p_row25_traceSegment_025_0216_0018, g32p_row25_traceSegment_025_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 252 9 9, g32p_row25_traceSegment_025_0252_0009, g32p_row25_traceSegment_025_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 270 9 9, g32p_row25_traceSegment_025_0270_0009, g32p_row25_traceSegment_025_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 252 18 18, g32p_row25_traceSegment_025_0252_0018, g32p_row25_traceSegment_025_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_025 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 216 36 36, g32p_row25_traceSegment_025_0216_0036, g32p_row25_traceSegment_025_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_025 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 144 72 72, g32p_row25_traceSegment_025_0144_0072, g32p_row25_traceSegment_025_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_025 0 288 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 0 144 144, g32p_row25_traceSegment_025_0000_0144, g32p_row25_traceSegment_025_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 288 9 9, g32p_row25_traceSegment_025_0288_0009, g32p_row25_traceSegment_025_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 306 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 315 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 306 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 306 9 9, g32p_row25_traceSegment_025_0306_0009, g32p_row25_traceSegment_025_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 288 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 288 18 18, g32p_row25_traceSegment_025_0288_0018, g32p_row25_traceSegment_025_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 333 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 324 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 324 9 9, g32p_row25_traceSegment_025_0324_0009, g32p_row25_traceSegment_025_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 342 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 351 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 342 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 342 9 9, g32p_row25_traceSegment_025_0342_0009, g32p_row25_traceSegment_025_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 324 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 324 18 18, g32p_row25_traceSegment_025_0324_0018, g32p_row25_traceSegment_025_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_025 288 72 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 288 36 36, g32p_row25_traceSegment_025_0288_0036, g32p_row25_traceSegment_025_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 360 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 360 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 360 9 9, g32p_row25_traceSegment_025_0360_0009, g32p_row25_traceSegment_025_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 378 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 387 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 378 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 378 9 9, g32p_row25_traceSegment_025_0378_0009, g32p_row25_traceSegment_025_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 360 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 360 18 18, g32p_row25_traceSegment_025_0360_0018, g32p_row25_traceSegment_025_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 396 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 405 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 396 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 396 9 9, g32p_row25_traceSegment_025_0396_0009, g32p_row25_traceSegment_025_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 414 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 414 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 414 9 9, g32p_row25_traceSegment_025_0414_0009, g32p_row25_traceSegment_025_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 396 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 396 18 18, g32p_row25_traceSegment_025_0396_0018, g32p_row25_traceSegment_025_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_025 360 72 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 360 36 36, g32p_row25_traceSegment_025_0360_0036, g32p_row25_traceSegment_025_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_025 288 144 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 288 72 72, g32p_row25_traceSegment_025_0288_0072, g32p_row25_traceSegment_025_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 441 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 432 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 432 9 9, g32p_row25_traceSegment_025_0432_0009, g32p_row25_traceSegment_025_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 450 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 450 9 9, g32p_row25_traceSegment_025_0450_0009, g32p_row25_traceSegment_025_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 432 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 432 18 18, g32p_row25_traceSegment_025_0432_0018, g32p_row25_traceSegment_025_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 468 9 9, g32p_row25_traceSegment_025_0468_0009, g32p_row25_traceSegment_025_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 486 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 486 9 9, g32p_row25_traceSegment_025_0486_0009, g32p_row25_traceSegment_025_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 468 18 18, g32p_row25_traceSegment_025_0468_0018, g32p_row25_traceSegment_025_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_025 432 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 432 36 36, g32p_row25_traceSegment_025_0432_0036, g32p_row25_traceSegment_025_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 504 9 9, g32p_row25_traceSegment_025_0504_0009, g32p_row25_traceSegment_025_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 522 9 9, g32p_row25_traceSegment_025_0522_0009, g32p_row25_traceSegment_025_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 504 18 18, g32p_row25_traceSegment_025_0504_0018, g32p_row25_traceSegment_025_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 540 9 9, g32p_row25_traceSegment_025_0540_0009, g32p_row25_traceSegment_025_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_025 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_025_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_025 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 558 9 9, g32p_row25_traceSegment_025_0558_0009, g32p_row25_traceSegment_025_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_025 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 540 18 18, g32p_row25_traceSegment_025_0540_0018, g32p_row25_traceSegment_025_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_025 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 504 36 36, g32p_row25_traceSegment_025_0504_0036, g32p_row25_traceSegment_025_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_025 432 144 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 432 72 72, g32p_row25_traceSegment_025_0432_0072, g32p_row25_traceSegment_025_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_025 288 288 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 288 144 144, g32p_row25_traceSegment_025_0288_0144, g32p_row25_traceSegment_025_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_025_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_025 0 576 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_025 0 288 288, g32p_row25_traceSegment_025_0000_0288, g32p_row25_traceSegment_025_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 25 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_025_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_029 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 29 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_029_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 9 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 0 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 0 9 9, g32p_row25_traceSegment_029_0000_0009, g32p_row25_traceSegment_029_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 18 9 9, g32p_row25_traceSegment_029_0018_0009, g32p_row25_traceSegment_029_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 0 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 0 18 18, g32p_row25_traceSegment_029_0000_0018, g32p_row25_traceSegment_029_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 36 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 36 9 9, g32p_row25_traceSegment_029_0036_0009, g32p_row25_traceSegment_029_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 54 9 9, g32p_row25_traceSegment_029_0054_0009, g32p_row25_traceSegment_029_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 36 18 18, g32p_row25_traceSegment_029_0036_0018, g32p_row25_traceSegment_029_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_029 0 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 0 36 36, g32p_row25_traceSegment_029_0000_0036, g32p_row25_traceSegment_029_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 72 9 9, g32p_row25_traceSegment_029_0072_0009, g32p_row25_traceSegment_029_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 90 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 90 9 9, g32p_row25_traceSegment_029_0090_0009, g32p_row25_traceSegment_029_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 72 18 18, g32p_row25_traceSegment_029_0072_0018, g32p_row25_traceSegment_029_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 108 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 108 9 9, g32p_row25_traceSegment_029_0108_0009, g32p_row25_traceSegment_029_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 126 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 126 9 9, g32p_row25_traceSegment_029_0126_0009, g32p_row25_traceSegment_029_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 108 18 18, g32p_row25_traceSegment_029_0108_0018, g32p_row25_traceSegment_029_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_029 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 72 36 36, g32p_row25_traceSegment_029_0072_0036, g32p_row25_traceSegment_029_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_029 0 144 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 0 72 72, g32p_row25_traceSegment_029_0000_0072, g32p_row25_traceSegment_029_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 144 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 153 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 144 9 9, g32p_row25_traceSegment_029_0144_0009, g32p_row25_traceSegment_029_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 162 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 162 9 9, g32p_row25_traceSegment_029_0162_0009, g32p_row25_traceSegment_029_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 144 18 18, g32p_row25_traceSegment_029_0144_0018, g32p_row25_traceSegment_029_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 180 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 189 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 180 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 180 9 9, g32p_row25_traceSegment_029_0180_0009, g32p_row25_traceSegment_029_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 198 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 207 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 198 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 198 9 9, g32p_row25_traceSegment_029_0198_0009, g32p_row25_traceSegment_029_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 180 36 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 180 18 18, g32p_row25_traceSegment_029_0180_0018, g32p_row25_traceSegment_029_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_029 144 72 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 144 36 36, g32p_row25_traceSegment_029_0144_0036, g32p_row25_traceSegment_029_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 216 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 225 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 216 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 216 9 9, g32p_row25_traceSegment_029_0216_0009, g32p_row25_traceSegment_029_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 234 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 243 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 234 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 234 9 9, g32p_row25_traceSegment_029_0234_0009, g32p_row25_traceSegment_029_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 216 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 216 18 18, g32p_row25_traceSegment_029_0216_0018, g32p_row25_traceSegment_029_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 252 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 261 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 252 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 252 9 9, g32p_row25_traceSegment_029_0252_0009, g32p_row25_traceSegment_029_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 270 9 9, g32p_row25_traceSegment_029_0270_0009, g32p_row25_traceSegment_029_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 252 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 252 18 18, g32p_row25_traceSegment_029_0252_0018, g32p_row25_traceSegment_029_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_029 216 72 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 216 36 36, g32p_row25_traceSegment_029_0216_0036, g32p_row25_traceSegment_029_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_029 144 144 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 144 72 72, g32p_row25_traceSegment_029_0144_0072, g32p_row25_traceSegment_029_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_029 0 288 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 0 144 144, g32p_row25_traceSegment_029_0000_0144, g32p_row25_traceSegment_029_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 288 9 9, g32p_row25_traceSegment_029_0288_0009, g32p_row25_traceSegment_029_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 306 9 9, g32p_row25_traceSegment_029_0306_0009, g32p_row25_traceSegment_029_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 288 18 18, g32p_row25_traceSegment_029_0288_0018, g32p_row25_traceSegment_029_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 333 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 324 9 9, g32p_row25_traceSegment_029_0324_0009, g32p_row25_traceSegment_029_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 351 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 342 9 9, g32p_row25_traceSegment_029_0342_0009, g32p_row25_traceSegment_029_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 324 18 18, g32p_row25_traceSegment_029_0324_0018, g32p_row25_traceSegment_029_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_029 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 288 36 36, g32p_row25_traceSegment_029_0288_0036, g32p_row25_traceSegment_029_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 360 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 360 9 9, g32p_row25_traceSegment_029_0360_0009, g32p_row25_traceSegment_029_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 378 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 387 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 378 9 9, g32p_row25_traceSegment_029_0378_0009, g32p_row25_traceSegment_029_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 360 18 18, g32p_row25_traceSegment_029_0360_0018, g32p_row25_traceSegment_029_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 396 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 405 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 396 9 9, g32p_row25_traceSegment_029_0396_0009, g32p_row25_traceSegment_029_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 414 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 414 9 9, g32p_row25_traceSegment_029_0414_0009, g32p_row25_traceSegment_029_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 396 18 18, g32p_row25_traceSegment_029_0396_0018, g32p_row25_traceSegment_029_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_029 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 360 36 36, g32p_row25_traceSegment_029_0360_0036, g32p_row25_traceSegment_029_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_029 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 288 72 72, g32p_row25_traceSegment_029_0288_0072, g32p_row25_traceSegment_029_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 441 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 432 9 9, g32p_row25_traceSegment_029_0432_0009, g32p_row25_traceSegment_029_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 450 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 450 9 9, g32p_row25_traceSegment_029_0450_0009, g32p_row25_traceSegment_029_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 432 18 18, g32p_row25_traceSegment_029_0432_0018, g32p_row25_traceSegment_029_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 468 9 9, g32p_row25_traceSegment_029_0468_0009, g32p_row25_traceSegment_029_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 486 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 486 9 9, g32p_row25_traceSegment_029_0486_0009, g32p_row25_traceSegment_029_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 468 18 18, g32p_row25_traceSegment_029_0468_0018, g32p_row25_traceSegment_029_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_029 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 432 36 36, g32p_row25_traceSegment_029_0432_0036, g32p_row25_traceSegment_029_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 504 9 9, g32p_row25_traceSegment_029_0504_0009, g32p_row25_traceSegment_029_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 522 9 9, g32p_row25_traceSegment_029_0522_0009, g32p_row25_traceSegment_029_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 504 18 18, g32p_row25_traceSegment_029_0504_0018, g32p_row25_traceSegment_029_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 540 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 540 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 540 9 9, g32p_row25_traceSegment_029_0540_0009, g32p_row25_traceSegment_029_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 558 9 = [0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_029 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_029_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_029 558 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 558 9 9, g32p_row25_traceSegment_029_0558_0009, g32p_row25_traceSegment_029_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_029 540 36 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 540 18 18, g32p_row25_traceSegment_029_0540_0018, g32p_row25_traceSegment_029_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_029 504 72 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 504 36 36, g32p_row25_traceSegment_029_0504_0036, g32p_row25_traceSegment_029_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_029 432 144 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 432 72 72, g32p_row25_traceSegment_029_0432_0072, g32p_row25_traceSegment_029_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_029 288 288 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 288 144 144, g32p_row25_traceSegment_029_0288_0144, g32p_row25_traceSegment_029_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_029_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_029 0 576 = [0, 16] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_029 0 288 288, g32p_row25_traceSegment_029_0000_0288, g32p_row25_traceSegment_029_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 29 = [0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_029_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_030 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 30 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_030_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 0 9 9, g32p_row25_traceSegment_030_0000_0009, g32p_row25_traceSegment_030_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 18 9 9, g32p_row25_traceSegment_030_0018_0009, g32p_row25_traceSegment_030_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 0 18 18, g32p_row25_traceSegment_030_0000_0018, g32p_row25_traceSegment_030_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 36 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 36 9 9, g32p_row25_traceSegment_030_0036_0009, g32p_row25_traceSegment_030_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 54 9 9, g32p_row25_traceSegment_030_0054_0009, g32p_row25_traceSegment_030_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 36 18 18, g32p_row25_traceSegment_030_0036_0018, g32p_row25_traceSegment_030_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_030 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 0 36 36, g32p_row25_traceSegment_030_0000_0036, g32p_row25_traceSegment_030_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 72 9 9, g32p_row25_traceSegment_030_0072_0009, g32p_row25_traceSegment_030_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 90 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 90 9 9, g32p_row25_traceSegment_030_0090_0009, g32p_row25_traceSegment_030_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 72 18 18, g32p_row25_traceSegment_030_0072_0018, g32p_row25_traceSegment_030_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 108 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 108 9 9, g32p_row25_traceSegment_030_0108_0009, g32p_row25_traceSegment_030_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 126 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 126 9 9, g32p_row25_traceSegment_030_0126_0009, g32p_row25_traceSegment_030_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 108 18 18, g32p_row25_traceSegment_030_0108_0018, g32p_row25_traceSegment_030_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_030 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 72 36 36, g32p_row25_traceSegment_030_0072_0036, g32p_row25_traceSegment_030_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_030 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 0 72 72, g32p_row25_traceSegment_030_0000_0072, g32p_row25_traceSegment_030_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 144 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 153 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 144 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 144 9 9, g32p_row25_traceSegment_030_0144_0009, g32p_row25_traceSegment_030_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 162 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 171 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 162 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 162 9 9, g32p_row25_traceSegment_030_0162_0009, g32p_row25_traceSegment_030_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 144 36 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 144 18 18, g32p_row25_traceSegment_030_0144_0018, g32p_row25_traceSegment_030_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 180 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 189 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 180 18 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 180 9 9, g32p_row25_traceSegment_030_0180_0009, g32p_row25_traceSegment_030_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 198 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 207 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 198 9 9, g32p_row25_traceSegment_030_0198_0009, g32p_row25_traceSegment_030_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 180 36 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 180 18 18, g32p_row25_traceSegment_030_0180_0018, g32p_row25_traceSegment_030_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_030 144 72 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 144 36 36, g32p_row25_traceSegment_030_0144_0036, g32p_row25_traceSegment_030_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 216 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 225 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 216 18 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 216 9 9, g32p_row25_traceSegment_030_0216_0009, g32p_row25_traceSegment_030_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 234 9 9, g32p_row25_traceSegment_030_0234_0009, g32p_row25_traceSegment_030_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 216 36 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 216 18 18, g32p_row25_traceSegment_030_0216_0018, g32p_row25_traceSegment_030_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 252 9 9, g32p_row25_traceSegment_030_0252_0009, g32p_row25_traceSegment_030_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 270 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 270 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 270 9 9, g32p_row25_traceSegment_030_0270_0009, g32p_row25_traceSegment_030_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 252 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 252 18 18, g32p_row25_traceSegment_030_0252_0018, g32p_row25_traceSegment_030_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_030 216 72 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 216 36 36, g32p_row25_traceSegment_030_0216_0036, g32p_row25_traceSegment_030_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_030 144 144 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 144 72 72, g32p_row25_traceSegment_030_0144_0072, g32p_row25_traceSegment_030_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_030 0 288 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 0 144 144, g32p_row25_traceSegment_030_0000_0144, g32p_row25_traceSegment_030_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 288 9 9, g32p_row25_traceSegment_030_0288_0009, g32p_row25_traceSegment_030_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 306 9 9, g32p_row25_traceSegment_030_0306_0009, g32p_row25_traceSegment_030_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 288 18 18, g32p_row25_traceSegment_030_0288_0018, g32p_row25_traceSegment_030_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 333 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 324 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 324 9 9, g32p_row25_traceSegment_030_0324_0009, g32p_row25_traceSegment_030_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 351 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 342 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 342 9 9, g32p_row25_traceSegment_030_0342_0009, g32p_row25_traceSegment_030_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 324 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 324 18 18, g32p_row25_traceSegment_030_0324_0018, g32p_row25_traceSegment_030_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_030 288 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 288 36 36, g32p_row25_traceSegment_030_0288_0036, g32p_row25_traceSegment_030_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 360 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 360 9 9, g32p_row25_traceSegment_030_0360_0009, g32p_row25_traceSegment_030_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 378 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 387 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 378 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 378 9 9, g32p_row25_traceSegment_030_0378_0009, g32p_row25_traceSegment_030_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 360 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 360 18 18, g32p_row25_traceSegment_030_0360_0018, g32p_row25_traceSegment_030_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 396 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 405 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 396 9 9, g32p_row25_traceSegment_030_0396_0009, g32p_row25_traceSegment_030_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 414 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 414 9 9, g32p_row25_traceSegment_030_0414_0009, g32p_row25_traceSegment_030_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 396 18 18, g32p_row25_traceSegment_030_0396_0018, g32p_row25_traceSegment_030_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_030 360 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 360 36 36, g32p_row25_traceSegment_030_0360_0036, g32p_row25_traceSegment_030_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_030 288 144 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 288 72 72, g32p_row25_traceSegment_030_0288_0072, g32p_row25_traceSegment_030_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 441 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 432 9 9, g32p_row25_traceSegment_030_0432_0009, g32p_row25_traceSegment_030_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 450 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 450 9 9, g32p_row25_traceSegment_030_0450_0009, g32p_row25_traceSegment_030_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 432 18 18, g32p_row25_traceSegment_030_0432_0018, g32p_row25_traceSegment_030_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 468 9 9, g32p_row25_traceSegment_030_0468_0009, g32p_row25_traceSegment_030_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 486 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 486 9 9, g32p_row25_traceSegment_030_0486_0009, g32p_row25_traceSegment_030_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 468 18 18, g32p_row25_traceSegment_030_0468_0018, g32p_row25_traceSegment_030_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_030 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 432 36 36, g32p_row25_traceSegment_030_0432_0036, g32p_row25_traceSegment_030_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 504 9 9, g32p_row25_traceSegment_030_0504_0009, g32p_row25_traceSegment_030_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 522 9 9, g32p_row25_traceSegment_030_0522_0009, g32p_row25_traceSegment_030_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 504 18 18, g32p_row25_traceSegment_030_0504_0018, g32p_row25_traceSegment_030_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 540 9 9, g32p_row25_traceSegment_030_0540_0009, g32p_row25_traceSegment_030_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_030 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_030_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_030 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 558 9 9, g32p_row25_traceSegment_030_0558_0009, g32p_row25_traceSegment_030_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_030 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 540 18 18, g32p_row25_traceSegment_030_0540_0018, g32p_row25_traceSegment_030_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_030 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 504 36 36, g32p_row25_traceSegment_030_0504_0036, g32p_row25_traceSegment_030_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_030 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 432 72 72, g32p_row25_traceSegment_030_0432_0072, g32p_row25_traceSegment_030_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_030 288 288 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 288 144 144, g32p_row25_traceSegment_030_0288_0144, g32p_row25_traceSegment_030_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_030_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_030 0 576 = [0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_030 0 288 288, g32p_row25_traceSegment_030_0000_0288, g32p_row25_traceSegment_030_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_030 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 30 = [0, 0, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_030_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_031 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 31 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_031_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 0 9 9, g32p_row25_traceSegment_031_0000_0009, g32p_row25_traceSegment_031_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 18 9 9, g32p_row25_traceSegment_031_0018_0009, g32p_row25_traceSegment_031_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 0 18 18, g32p_row25_traceSegment_031_0000_0018, g32p_row25_traceSegment_031_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 36 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 36 9 9, g32p_row25_traceSegment_031_0036_0009, g32p_row25_traceSegment_031_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 54 9 9, g32p_row25_traceSegment_031_0054_0009, g32p_row25_traceSegment_031_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 36 18 18, g32p_row25_traceSegment_031_0036_0018, g32p_row25_traceSegment_031_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_031 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 0 36 36, g32p_row25_traceSegment_031_0000_0036, g32p_row25_traceSegment_031_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 72 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 72 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 72 9 9, g32p_row25_traceSegment_031_0072_0009, g32p_row25_traceSegment_031_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 90 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 90 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 90 9 9, g32p_row25_traceSegment_031_0090_0009, g32p_row25_traceSegment_031_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 72 36 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 72 18 18, g32p_row25_traceSegment_031_0072_0018, g32p_row25_traceSegment_031_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 108 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 108 9 9, g32p_row25_traceSegment_031_0108_0009, g32p_row25_traceSegment_031_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 126 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 126 9 9, g32p_row25_traceSegment_031_0126_0009, g32p_row25_traceSegment_031_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 108 18 18, g32p_row25_traceSegment_031_0108_0018, g32p_row25_traceSegment_031_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_031 72 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 72 36 36, g32p_row25_traceSegment_031_0072_0036, g32p_row25_traceSegment_031_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_031 0 144 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 0 72 72, g32p_row25_traceSegment_031_0000_0072, g32p_row25_traceSegment_031_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 144 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 153 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 144 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 144 9 9, g32p_row25_traceSegment_031_0144_0009, g32p_row25_traceSegment_031_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 162 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 171 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 162 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 162 9 9, g32p_row25_traceSegment_031_0162_0009, g32p_row25_traceSegment_031_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 144 36 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 144 18 18, g32p_row25_traceSegment_031_0144_0018, g32p_row25_traceSegment_031_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 180 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 189 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 180 9 9, g32p_row25_traceSegment_031_0180_0009, g32p_row25_traceSegment_031_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 198 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 207 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 198 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 198 9 9, g32p_row25_traceSegment_031_0198_0009, g32p_row25_traceSegment_031_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 180 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 180 18 18, g32p_row25_traceSegment_031_0180_0018, g32p_row25_traceSegment_031_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_031 144 72 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 144 36 36, g32p_row25_traceSegment_031_0144_0036, g32p_row25_traceSegment_031_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 216 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 225 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 216 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 216 9 9, g32p_row25_traceSegment_031_0216_0009, g32p_row25_traceSegment_031_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 234 9 9, g32p_row25_traceSegment_031_0234_0009, g32p_row25_traceSegment_031_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 216 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 216 18 18, g32p_row25_traceSegment_031_0216_0018, g32p_row25_traceSegment_031_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 261 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 252 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 252 9 9, g32p_row25_traceSegment_031_0252_0009, g32p_row25_traceSegment_031_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 270 9 9, g32p_row25_traceSegment_031_0270_0009, g32p_row25_traceSegment_031_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 252 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 252 18 18, g32p_row25_traceSegment_031_0252_0018, g32p_row25_traceSegment_031_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_031 216 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 216 36 36, g32p_row25_traceSegment_031_0216_0036, g32p_row25_traceSegment_031_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_031 144 144 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 144 72 72, g32p_row25_traceSegment_031_0144_0072, g32p_row25_traceSegment_031_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_031 0 288 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 0 144 144, g32p_row25_traceSegment_031_0000_0144, g32p_row25_traceSegment_031_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 288 9 9, g32p_row25_traceSegment_031_0288_0009, g32p_row25_traceSegment_031_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 306 9 9, g32p_row25_traceSegment_031_0306_0009, g32p_row25_traceSegment_031_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 288 18 18, g32p_row25_traceSegment_031_0288_0018, g32p_row25_traceSegment_031_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 333 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 324 9 9, g32p_row25_traceSegment_031_0324_0009, g32p_row25_traceSegment_031_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 351 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 342 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 342 9 9, g32p_row25_traceSegment_031_0342_0009, g32p_row25_traceSegment_031_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 324 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 324 18 18, g32p_row25_traceSegment_031_0324_0018, g32p_row25_traceSegment_031_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_031 288 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 288 36 36, g32p_row25_traceSegment_031_0288_0036, g32p_row25_traceSegment_031_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 360 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 360 9 9, g32p_row25_traceSegment_031_0360_0009, g32p_row25_traceSegment_031_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 378 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 387 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 378 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 378 9 9, g32p_row25_traceSegment_031_0378_0009, g32p_row25_traceSegment_031_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 360 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 360 18 18, g32p_row25_traceSegment_031_0360_0018, g32p_row25_traceSegment_031_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 405 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 396 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 396 9 9, g32p_row25_traceSegment_031_0396_0009, g32p_row25_traceSegment_031_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 414 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 414 9 9, g32p_row25_traceSegment_031_0414_0009, g32p_row25_traceSegment_031_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 396 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 396 18 18, g32p_row25_traceSegment_031_0396_0018, g32p_row25_traceSegment_031_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_031 360 72 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 360 36 36, g32p_row25_traceSegment_031_0360_0036, g32p_row25_traceSegment_031_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_031 288 144 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 288 72 72, g32p_row25_traceSegment_031_0288_0072, g32p_row25_traceSegment_031_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 441 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 432 9 9, g32p_row25_traceSegment_031_0432_0009, g32p_row25_traceSegment_031_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 450 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 450 9 9, g32p_row25_traceSegment_031_0450_0009, g32p_row25_traceSegment_031_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 432 18 18, g32p_row25_traceSegment_031_0432_0018, g32p_row25_traceSegment_031_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 468 9 9, g32p_row25_traceSegment_031_0468_0009, g32p_row25_traceSegment_031_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 486 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 486 9 9, g32p_row25_traceSegment_031_0486_0009, g32p_row25_traceSegment_031_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 468 18 18, g32p_row25_traceSegment_031_0468_0018, g32p_row25_traceSegment_031_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_031 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 432 36 36, g32p_row25_traceSegment_031_0432_0036, g32p_row25_traceSegment_031_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 504 9 9, g32p_row25_traceSegment_031_0504_0009, g32p_row25_traceSegment_031_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 522 9 9, g32p_row25_traceSegment_031_0522_0009, g32p_row25_traceSegment_031_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 504 18 18, g32p_row25_traceSegment_031_0504_0018, g32p_row25_traceSegment_031_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 540 9 9, g32p_row25_traceSegment_031_0540_0009, g32p_row25_traceSegment_031_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_031 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_031_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_031 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 558 9 9, g32p_row25_traceSegment_031_0558_0009, g32p_row25_traceSegment_031_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_031 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 540 18 18, g32p_row25_traceSegment_031_0540_0018, g32p_row25_traceSegment_031_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_031 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 504 36 36, g32p_row25_traceSegment_031_0504_0036, g32p_row25_traceSegment_031_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_031 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 432 72 72, g32p_row25_traceSegment_031_0432_0072, g32p_row25_traceSegment_031_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_031 288 288 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 288 144 144, g32p_row25_traceSegment_031_0288_0144, g32p_row25_traceSegment_031_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_031_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_031 0 576 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_031 0 288 288, g32p_row25_traceSegment_031_0000_0288, g32p_row25_traceSegment_031_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 31 = [0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_031_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_034 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 34 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_034_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 0 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 0 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 0 9 9, g32p_row25_traceSegment_034_0000_0009, g32p_row25_traceSegment_034_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 18 9 9, g32p_row25_traceSegment_034_0018_0009, g32p_row25_traceSegment_034_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 0 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 0 18 18, g32p_row25_traceSegment_034_0000_0018, g32p_row25_traceSegment_034_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 36 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 36 9 9, g32p_row25_traceSegment_034_0036_0009, g32p_row25_traceSegment_034_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 54 9 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 63 9 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 54 18 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 54 9 9, g32p_row25_traceSegment_034_0054_0009, g32p_row25_traceSegment_034_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 36 36 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 36 18 18, g32p_row25_traceSegment_034_0036_0018, g32p_row25_traceSegment_034_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_034 0 72 = [0, 2, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 0 36 36, g32p_row25_traceSegment_034_0000_0036, g32p_row25_traceSegment_034_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 72 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 81 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 72 18 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 72 9 9, g32p_row25_traceSegment_034_0072_0009, g32p_row25_traceSegment_034_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 90 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 99 9 = [0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 90 18 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 90 9 9, g32p_row25_traceSegment_034_0090_0009, g32p_row25_traceSegment_034_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 72 36 = [0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 72 18 18, g32p_row25_traceSegment_034_0072_0018, g32p_row25_traceSegment_034_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 108 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 117 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 108 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 108 9 9, g32p_row25_traceSegment_034_0108_0009, g32p_row25_traceSegment_034_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 126 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 135 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 126 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 126 9 9, g32p_row25_traceSegment_034_0126_0009, g32p_row25_traceSegment_034_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 108 36 = [0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 108 18 18, g32p_row25_traceSegment_034_0108_0018, g32p_row25_traceSegment_034_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_034 72 72 = [0, 5, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 72 36 36, g32p_row25_traceSegment_034_0072_0036, g32p_row25_traceSegment_034_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_034 0 144 = [0, 7, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 0 72 72, g32p_row25_traceSegment_034_0000_0072, g32p_row25_traceSegment_034_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 144 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 153 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 144 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 144 9 9, g32p_row25_traceSegment_034_0144_0009, g32p_row25_traceSegment_034_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 162 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 162 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 162 9 9, g32p_row25_traceSegment_034_0162_0009, g32p_row25_traceSegment_034_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 144 36 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 144 18 18, g32p_row25_traceSegment_034_0144_0018, g32p_row25_traceSegment_034_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 180 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 189 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 180 9 9, g32p_row25_traceSegment_034_0180_0009, g32p_row25_traceSegment_034_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 198 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 207 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 198 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 198 9 9, g32p_row25_traceSegment_034_0198_0009, g32p_row25_traceSegment_034_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 180 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 180 18 18, g32p_row25_traceSegment_034_0180_0018, g32p_row25_traceSegment_034_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_034 144 72 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 144 36 36, g32p_row25_traceSegment_034_0144_0036, g32p_row25_traceSegment_034_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 216 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 225 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 216 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 216 9 9, g32p_row25_traceSegment_034_0216_0009, g32p_row25_traceSegment_034_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 234 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 243 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 234 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 234 9 9, g32p_row25_traceSegment_034_0234_0009, g32p_row25_traceSegment_034_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 216 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 216 18 18, g32p_row25_traceSegment_034_0216_0018, g32p_row25_traceSegment_034_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 252 9 9, g32p_row25_traceSegment_034_0252_0009, g32p_row25_traceSegment_034_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 270 9 9, g32p_row25_traceSegment_034_0270_0009, g32p_row25_traceSegment_034_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 252 18 18, g32p_row25_traceSegment_034_0252_0018, g32p_row25_traceSegment_034_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_034 216 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 216 36 36, g32p_row25_traceSegment_034_0216_0036, g32p_row25_traceSegment_034_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_034 144 144 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 144 72 72, g32p_row25_traceSegment_034_0144_0072, g32p_row25_traceSegment_034_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_034 0 288 = [0, 7, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 0 144 144, g32p_row25_traceSegment_034_0000_0144, g32p_row25_traceSegment_034_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 288 9 9, g32p_row25_traceSegment_034_0288_0009, g32p_row25_traceSegment_034_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 306 9 9, g32p_row25_traceSegment_034_0306_0009, g32p_row25_traceSegment_034_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 288 18 18, g32p_row25_traceSegment_034_0288_0018, g32p_row25_traceSegment_034_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 333 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 324 9 9, g32p_row25_traceSegment_034_0324_0009, g32p_row25_traceSegment_034_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 351 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 342 9 9, g32p_row25_traceSegment_034_0342_0009, g32p_row25_traceSegment_034_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 324 18 18, g32p_row25_traceSegment_034_0324_0018, g32p_row25_traceSegment_034_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_034 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 288 36 36, g32p_row25_traceSegment_034_0288_0036, g32p_row25_traceSegment_034_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 360 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 360 9 9, g32p_row25_traceSegment_034_0360_0009, g32p_row25_traceSegment_034_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 378 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 387 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 378 18 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 378 9 9, g32p_row25_traceSegment_034_0378_0009, g32p_row25_traceSegment_034_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 360 36 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 360 18 18, g32p_row25_traceSegment_034_0360_0018, g32p_row25_traceSegment_034_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 405 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 396 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 396 9 9, g32p_row25_traceSegment_034_0396_0009, g32p_row25_traceSegment_034_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 414 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 423 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 414 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 414 9 9, g32p_row25_traceSegment_034_0414_0009, g32p_row25_traceSegment_034_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 396 36 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 396 18 18, g32p_row25_traceSegment_034_0396_0018, g32p_row25_traceSegment_034_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_034 360 72 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 360 36 36, g32p_row25_traceSegment_034_0360_0036, g32p_row25_traceSegment_034_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_034 288 144 = [0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 288 72 72, g32p_row25_traceSegment_034_0288_0072, g32p_row25_traceSegment_034_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 432 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 441 9 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 432 18 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 432 9 9, g32p_row25_traceSegment_034_0432_0009, g32p_row25_traceSegment_034_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 450 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 459 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 450 18 = [0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 450 9 9, g32p_row25_traceSegment_034_0450_0009, g32p_row25_traceSegment_034_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 432 36 = [0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 432 18 18, g32p_row25_traceSegment_034_0432_0018, g32p_row25_traceSegment_034_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 468 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 468 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 468 9 9, g32p_row25_traceSegment_034_0468_0009, g32p_row25_traceSegment_034_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 486 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 486 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 486 9 9, g32p_row25_traceSegment_034_0486_0009, g32p_row25_traceSegment_034_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 468 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 468 18 18, g32p_row25_traceSegment_034_0468_0018, g32p_row25_traceSegment_034_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_034 432 72 = [0, 2, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 432 36 36, g32p_row25_traceSegment_034_0432_0036, g32p_row25_traceSegment_034_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 504 9 9, g32p_row25_traceSegment_034_0504_0009, g32p_row25_traceSegment_034_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 522 9 9, g32p_row25_traceSegment_034_0522_0009, g32p_row25_traceSegment_034_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 504 18 18, g32p_row25_traceSegment_034_0504_0018, g32p_row25_traceSegment_034_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 549 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 540 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 540 9 9, g32p_row25_traceSegment_034_0540_0009, g32p_row25_traceSegment_034_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 558 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_034 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_034_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_034 558 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 558 9 9, g32p_row25_traceSegment_034_0558_0009, g32p_row25_traceSegment_034_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_034 540 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 540 18 18, g32p_row25_traceSegment_034_0540_0018, g32p_row25_traceSegment_034_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_034 504 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 504 36 36, g32p_row25_traceSegment_034_0504_0036, g32p_row25_traceSegment_034_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_034 432 144 = [0, 2, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 432 72 72, g32p_row25_traceSegment_034_0432_0072, g32p_row25_traceSegment_034_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_034 288 288 = [0, 5, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 288 144 144, g32p_row25_traceSegment_034_0288_0144, g32p_row25_traceSegment_034_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_034_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_034 0 576 = [0, 12, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_034 0 288 288, g32p_row25_traceSegment_034_0000_0288, g32p_row25_traceSegment_034_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 34 = [0, 12, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_034_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_037 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 37 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_037_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 0 9 9, g32p_row25_traceSegment_037_0000_0009, g32p_row25_traceSegment_037_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 18 9 9, g32p_row25_traceSegment_037_0018_0009, g32p_row25_traceSegment_037_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 0 18 18, g32p_row25_traceSegment_037_0000_0018, g32p_row25_traceSegment_037_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 36 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 36 9 9, g32p_row25_traceSegment_037_0036_0009, g32p_row25_traceSegment_037_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 54 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 54 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 54 9 9, g32p_row25_traceSegment_037_0054_0009, g32p_row25_traceSegment_037_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 36 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 36 18 18, g32p_row25_traceSegment_037_0036_0018, g32p_row25_traceSegment_037_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_037 0 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 0 36 36, g32p_row25_traceSegment_037_0000_0036, g32p_row25_traceSegment_037_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 72 9 9, g32p_row25_traceSegment_037_0072_0009, g32p_row25_traceSegment_037_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 90 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 90 9 9, g32p_row25_traceSegment_037_0090_0009, g32p_row25_traceSegment_037_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 72 18 18, g32p_row25_traceSegment_037_0072_0018, g32p_row25_traceSegment_037_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 108 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 108 9 9, g32p_row25_traceSegment_037_0108_0009, g32p_row25_traceSegment_037_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 126 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 126 9 9, g32p_row25_traceSegment_037_0126_0009, g32p_row25_traceSegment_037_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 108 18 18, g32p_row25_traceSegment_037_0108_0018, g32p_row25_traceSegment_037_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_037 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 72 36 36, g32p_row25_traceSegment_037_0072_0036, g32p_row25_traceSegment_037_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_037 0 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 0 72 72, g32p_row25_traceSegment_037_0000_0072, g32p_row25_traceSegment_037_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 144 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 153 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 144 9 9, g32p_row25_traceSegment_037_0144_0009, g32p_row25_traceSegment_037_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 162 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 162 9 9, g32p_row25_traceSegment_037_0162_0009, g32p_row25_traceSegment_037_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 144 18 18, g32p_row25_traceSegment_037_0144_0018, g32p_row25_traceSegment_037_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 180 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 189 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 180 9 9, g32p_row25_traceSegment_037_0180_0009, g32p_row25_traceSegment_037_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 198 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 207 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 198 9 9, g32p_row25_traceSegment_037_0198_0009, g32p_row25_traceSegment_037_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 180 18 18, g32p_row25_traceSegment_037_0180_0018, g32p_row25_traceSegment_037_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_037 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 144 36 36, g32p_row25_traceSegment_037_0144_0036, g32p_row25_traceSegment_037_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 216 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 225 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 216 9 9, g32p_row25_traceSegment_037_0216_0009, g32p_row25_traceSegment_037_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 234 9 9, g32p_row25_traceSegment_037_0234_0009, g32p_row25_traceSegment_037_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 216 18 18, g32p_row25_traceSegment_037_0216_0018, g32p_row25_traceSegment_037_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 252 9 9, g32p_row25_traceSegment_037_0252_0009, g32p_row25_traceSegment_037_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 270 9 9, g32p_row25_traceSegment_037_0270_0009, g32p_row25_traceSegment_037_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 252 18 18, g32p_row25_traceSegment_037_0252_0018, g32p_row25_traceSegment_037_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_037 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 216 36 36, g32p_row25_traceSegment_037_0216_0036, g32p_row25_traceSegment_037_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_037 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 144 72 72, g32p_row25_traceSegment_037_0144_0072, g32p_row25_traceSegment_037_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_037 0 288 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 0 144 144, g32p_row25_traceSegment_037_0000_0144, g32p_row25_traceSegment_037_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 288 9 9, g32p_row25_traceSegment_037_0288_0009, g32p_row25_traceSegment_037_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 306 9 9, g32p_row25_traceSegment_037_0306_0009, g32p_row25_traceSegment_037_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 288 18 18, g32p_row25_traceSegment_037_0288_0018, g32p_row25_traceSegment_037_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 333 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 324 9 9, g32p_row25_traceSegment_037_0324_0009, g32p_row25_traceSegment_037_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 351 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 342 9 9, g32p_row25_traceSegment_037_0342_0009, g32p_row25_traceSegment_037_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 324 18 18, g32p_row25_traceSegment_037_0324_0018, g32p_row25_traceSegment_037_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_037 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 288 36 36, g32p_row25_traceSegment_037_0288_0036, g32p_row25_traceSegment_037_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 360 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 360 9 9, g32p_row25_traceSegment_037_0360_0009, g32p_row25_traceSegment_037_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 378 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 387 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 378 9 9, g32p_row25_traceSegment_037_0378_0009, g32p_row25_traceSegment_037_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 360 18 18, g32p_row25_traceSegment_037_0360_0018, g32p_row25_traceSegment_037_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 396 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 405 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 396 9 9, g32p_row25_traceSegment_037_0396_0009, g32p_row25_traceSegment_037_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 414 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 414 9 9, g32p_row25_traceSegment_037_0414_0009, g32p_row25_traceSegment_037_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 396 18 18, g32p_row25_traceSegment_037_0396_0018, g32p_row25_traceSegment_037_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_037 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 360 36 36, g32p_row25_traceSegment_037_0360_0036, g32p_row25_traceSegment_037_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_037 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 288 72 72, g32p_row25_traceSegment_037_0288_0072, g32p_row25_traceSegment_037_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 441 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 432 9 9, g32p_row25_traceSegment_037_0432_0009, g32p_row25_traceSegment_037_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 450 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 450 9 9, g32p_row25_traceSegment_037_0450_0009, g32p_row25_traceSegment_037_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 432 18 18, g32p_row25_traceSegment_037_0432_0018, g32p_row25_traceSegment_037_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 468 9 9, g32p_row25_traceSegment_037_0468_0009, g32p_row25_traceSegment_037_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 486 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 486 9 9, g32p_row25_traceSegment_037_0486_0009, g32p_row25_traceSegment_037_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 468 18 18, g32p_row25_traceSegment_037_0468_0018, g32p_row25_traceSegment_037_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_037 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 432 36 36, g32p_row25_traceSegment_037_0432_0036, g32p_row25_traceSegment_037_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 504 9 9, g32p_row25_traceSegment_037_0504_0009, g32p_row25_traceSegment_037_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 522 9 9, g32p_row25_traceSegment_037_0522_0009, g32p_row25_traceSegment_037_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 504 18 18, g32p_row25_traceSegment_037_0504_0018, g32p_row25_traceSegment_037_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 540 9 9, g32p_row25_traceSegment_037_0540_0009, g32p_row25_traceSegment_037_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_037 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_037_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_037 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 558 9 9, g32p_row25_traceSegment_037_0558_0009, g32p_row25_traceSegment_037_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_037 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 540 18 18, g32p_row25_traceSegment_037_0540_0018, g32p_row25_traceSegment_037_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_037 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 504 36 36, g32p_row25_traceSegment_037_0504_0036, g32p_row25_traceSegment_037_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_037 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 432 72 72, g32p_row25_traceSegment_037_0432_0072, g32p_row25_traceSegment_037_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_037 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 288 144 144, g32p_row25_traceSegment_037_0288_0144, g32p_row25_traceSegment_037_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_037_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_037 0 576 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_037 0 288 288, g32p_row25_traceSegment_037_0000_0288, g32p_row25_traceSegment_037_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 37 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_037_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_038 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 38 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_038_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 0 9 9, g32p_row25_traceSegment_038_0000_0009, g32p_row25_traceSegment_038_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 18 9 = [1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 27 9 = [1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 18 18 = [2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 18 9 9, g32p_row25_traceSegment_038_0018_0009, g32p_row25_traceSegment_038_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 0 36 = [2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 0 18 18, g32p_row25_traceSegment_038_0000_0018, g32p_row25_traceSegment_038_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 36 9 = [2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 36 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 36 9 9, g32p_row25_traceSegment_038_0036_0009, g32p_row25_traceSegment_038_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 54 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 63 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 54 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 54 9 9, g32p_row25_traceSegment_038_0054_0009, g32p_row25_traceSegment_038_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 36 36 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 36 18 18, g32p_row25_traceSegment_038_0036_0018, g32p_row25_traceSegment_038_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_038 0 72 = [4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 0 36 36, g32p_row25_traceSegment_038_0000_0036, g32p_row25_traceSegment_038_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 72 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 81 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 72 18 = [1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 72 9 9, g32p_row25_traceSegment_038_0072_0009, g32p_row25_traceSegment_038_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 90 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 99 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 90 18 = [2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 90 9 9, g32p_row25_traceSegment_038_0090_0009, g32p_row25_traceSegment_038_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 72 36 = [3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 72 18 18, g32p_row25_traceSegment_038_0072_0018, g32p_row25_traceSegment_038_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 108 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 117 9 = [1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 108 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 108 9 9, g32p_row25_traceSegment_038_0108_0009, g32p_row25_traceSegment_038_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 126 9 = [2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 126 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 126 9 9, g32p_row25_traceSegment_038_0126_0009, g32p_row25_traceSegment_038_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 108 36 = [3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 108 18 18, g32p_row25_traceSegment_038_0108_0018, g32p_row25_traceSegment_038_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_038 72 72 = [6, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 72 36 36, g32p_row25_traceSegment_038_0072_0036, g32p_row25_traceSegment_038_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_038 0 144 = [10, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 0 72 72, g32p_row25_traceSegment_038_0000_0072, g32p_row25_traceSegment_038_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 144 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 153 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 144 9 9, g32p_row25_traceSegment_038_0144_0009, g32p_row25_traceSegment_038_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 162 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 162 9 9, g32p_row25_traceSegment_038_0162_0009, g32p_row25_traceSegment_038_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 144 18 18, g32p_row25_traceSegment_038_0144_0018, g32p_row25_traceSegment_038_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 180 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 189 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 180 18 = [1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 180 9 9, g32p_row25_traceSegment_038_0180_0009, g32p_row25_traceSegment_038_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 198 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 207 9 = [1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 198 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 198 9 9, g32p_row25_traceSegment_038_0198_0009, g32p_row25_traceSegment_038_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 180 36 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 180 18 18, g32p_row25_traceSegment_038_0180_0018, g32p_row25_traceSegment_038_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_038 144 72 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 144 36 36, g32p_row25_traceSegment_038_0144_0036, g32p_row25_traceSegment_038_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 216 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 225 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 216 9 9, g32p_row25_traceSegment_038_0216_0009, g32p_row25_traceSegment_038_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 234 9 9, g32p_row25_traceSegment_038_0234_0009, g32p_row25_traceSegment_038_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 216 18 18, g32p_row25_traceSegment_038_0216_0018, g32p_row25_traceSegment_038_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 252 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 261 9 = [3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 252 18 = [4, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 252 9 9, g32p_row25_traceSegment_038_0252_0009, g32p_row25_traceSegment_038_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 270 9 = [1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 279 9 = [1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 270 18 = [2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 270 9 9, g32p_row25_traceSegment_038_0270_0009, g32p_row25_traceSegment_038_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 252 36 = [6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 252 18 18, g32p_row25_traceSegment_038_0252_0018, g32p_row25_traceSegment_038_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_038 216 72 = [6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 216 36 36, g32p_row25_traceSegment_038_0216_0036, g32p_row25_traceSegment_038_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_038 144 144 = [8, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 144 72 72, g32p_row25_traceSegment_038_0144_0072, g32p_row25_traceSegment_038_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_038 0 288 = [18, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 0 144 144, g32p_row25_traceSegment_038_0000_0144, g32p_row25_traceSegment_038_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 288 9 9, g32p_row25_traceSegment_038_0288_0009, g32p_row25_traceSegment_038_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 306 9 9, g32p_row25_traceSegment_038_0306_0009, g32p_row25_traceSegment_038_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 288 18 18, g32p_row25_traceSegment_038_0288_0018, g32p_row25_traceSegment_038_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 333 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 324 9 9, g32p_row25_traceSegment_038_0324_0009, g32p_row25_traceSegment_038_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 351 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 342 9 9, g32p_row25_traceSegment_038_0342_0009, g32p_row25_traceSegment_038_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 324 18 18, g32p_row25_traceSegment_038_0324_0018, g32p_row25_traceSegment_038_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_038 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 288 36 36, g32p_row25_traceSegment_038_0288_0036, g32p_row25_traceSegment_038_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 360 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 360 9 9, g32p_row25_traceSegment_038_0360_0009, g32p_row25_traceSegment_038_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 378 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 387 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 378 9 9, g32p_row25_traceSegment_038_0378_0009, g32p_row25_traceSegment_038_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 360 18 18, g32p_row25_traceSegment_038_0360_0018, g32p_row25_traceSegment_038_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 396 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 405 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 396 9 9, g32p_row25_traceSegment_038_0396_0009, g32p_row25_traceSegment_038_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 414 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 414 9 9, g32p_row25_traceSegment_038_0414_0009, g32p_row25_traceSegment_038_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 396 18 18, g32p_row25_traceSegment_038_0396_0018, g32p_row25_traceSegment_038_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_038 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 360 36 36, g32p_row25_traceSegment_038_0360_0036, g32p_row25_traceSegment_038_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_038 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 288 72 72, g32p_row25_traceSegment_038_0288_0072, g32p_row25_traceSegment_038_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 441 9 = [1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 432 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 432 9 9, g32p_row25_traceSegment_038_0432_0009, g32p_row25_traceSegment_038_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 450 9 = [3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 459 9 = [2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 450 18 = [5, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 450 9 9, g32p_row25_traceSegment_038_0450_0009, g32p_row25_traceSegment_038_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 432 36 = [6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 432 18 18, g32p_row25_traceSegment_038_0432_0018, g32p_row25_traceSegment_038_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 468 9 9, g32p_row25_traceSegment_038_0468_0009, g32p_row25_traceSegment_038_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 486 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 486 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 486 9 9, g32p_row25_traceSegment_038_0486_0009, g32p_row25_traceSegment_038_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 468 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 468 18 18, g32p_row25_traceSegment_038_0468_0018, g32p_row25_traceSegment_038_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_038 432 72 = [6, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 432 36 36, g32p_row25_traceSegment_038_0432_0036, g32p_row25_traceSegment_038_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 504 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 504 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 504 9 9, g32p_row25_traceSegment_038_0504_0009, g32p_row25_traceSegment_038_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 522 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 522 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 522 9 9, g32p_row25_traceSegment_038_0522_0009, g32p_row25_traceSegment_038_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 504 36 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 504 18 18, g32p_row25_traceSegment_038_0504_0018, g32p_row25_traceSegment_038_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 540 9 9, g32p_row25_traceSegment_038_0540_0009, g32p_row25_traceSegment_038_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_038 567 9 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_038_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_038 558 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 558 9 9, g32p_row25_traceSegment_038_0558_0009, g32p_row25_traceSegment_038_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_038 540 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 540 18 18, g32p_row25_traceSegment_038_0540_0018, g32p_row25_traceSegment_038_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_038 504 72 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 504 36 36, g32p_row25_traceSegment_038_0504_0036, g32p_row25_traceSegment_038_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_038 432 144 = [6, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 432 72 72, g32p_row25_traceSegment_038_0432_0072, g32p_row25_traceSegment_038_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_038 288 288 = [6, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 288 144 144, g32p_row25_traceSegment_038_0288_0144, g32p_row25_traceSegment_038_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_038_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_038 0 576 = [24, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_038 0 288 288, g32p_row25_traceSegment_038_0000_0288, g32p_row25_traceSegment_038_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_038 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 38 = [24, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_038_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_043 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 43 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_043_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 0 9 9, g32p_row25_traceSegment_043_0000_0009, g32p_row25_traceSegment_043_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 18 9 9, g32p_row25_traceSegment_043_0018_0009, g32p_row25_traceSegment_043_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 0 18 18, g32p_row25_traceSegment_043_0000_0018, g32p_row25_traceSegment_043_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 36 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 36 9 9, g32p_row25_traceSegment_043_0036_0009, g32p_row25_traceSegment_043_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 54 9 9, g32p_row25_traceSegment_043_0054_0009, g32p_row25_traceSegment_043_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 36 18 18, g32p_row25_traceSegment_043_0036_0018, g32p_row25_traceSegment_043_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_043 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 0 36 36, g32p_row25_traceSegment_043_0000_0036, g32p_row25_traceSegment_043_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 81 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 72 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 72 9 9, g32p_row25_traceSegment_043_0072_0009, g32p_row25_traceSegment_043_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 90 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 90 9 9, g32p_row25_traceSegment_043_0090_0009, g32p_row25_traceSegment_043_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 72 36 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 72 18 18, g32p_row25_traceSegment_043_0072_0018, g32p_row25_traceSegment_043_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 108 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 117 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 108 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 108 9 9, g32p_row25_traceSegment_043_0108_0009, g32p_row25_traceSegment_043_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 126 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 126 9 9, g32p_row25_traceSegment_043_0126_0009, g32p_row25_traceSegment_043_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 108 36 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 108 18 18, g32p_row25_traceSegment_043_0108_0018, g32p_row25_traceSegment_043_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_043 72 72 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 72 36 36, g32p_row25_traceSegment_043_0072_0036, g32p_row25_traceSegment_043_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_043 0 144 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 0 72 72, g32p_row25_traceSegment_043_0000_0072, g32p_row25_traceSegment_043_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 144 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 153 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 144 9 9, g32p_row25_traceSegment_043_0144_0009, g32p_row25_traceSegment_043_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 162 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 162 9 9, g32p_row25_traceSegment_043_0162_0009, g32p_row25_traceSegment_043_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 144 18 18, g32p_row25_traceSegment_043_0144_0018, g32p_row25_traceSegment_043_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 180 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 189 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 180 9 9, g32p_row25_traceSegment_043_0180_0009, g32p_row25_traceSegment_043_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 198 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 207 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 198 9 9, g32p_row25_traceSegment_043_0198_0009, g32p_row25_traceSegment_043_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 180 18 18, g32p_row25_traceSegment_043_0180_0018, g32p_row25_traceSegment_043_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_043 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 144 36 36, g32p_row25_traceSegment_043_0144_0036, g32p_row25_traceSegment_043_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 216 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 225 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 216 9 9, g32p_row25_traceSegment_043_0216_0009, g32p_row25_traceSegment_043_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 234 9 9, g32p_row25_traceSegment_043_0234_0009, g32p_row25_traceSegment_043_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 216 18 18, g32p_row25_traceSegment_043_0216_0018, g32p_row25_traceSegment_043_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 252 9 9, g32p_row25_traceSegment_043_0252_0009, g32p_row25_traceSegment_043_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 270 9 9, g32p_row25_traceSegment_043_0270_0009, g32p_row25_traceSegment_043_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 252 18 18, g32p_row25_traceSegment_043_0252_0018, g32p_row25_traceSegment_043_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_043 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 216 36 36, g32p_row25_traceSegment_043_0216_0036, g32p_row25_traceSegment_043_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_043 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 144 72 72, g32p_row25_traceSegment_043_0144_0072, g32p_row25_traceSegment_043_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_043 0 288 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 0 144 144, g32p_row25_traceSegment_043_0000_0144, g32p_row25_traceSegment_043_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 288 9 9, g32p_row25_traceSegment_043_0288_0009, g32p_row25_traceSegment_043_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 306 9 9, g32p_row25_traceSegment_043_0306_0009, g32p_row25_traceSegment_043_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 288 18 18, g32p_row25_traceSegment_043_0288_0018, g32p_row25_traceSegment_043_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 333 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 324 9 9, g32p_row25_traceSegment_043_0324_0009, g32p_row25_traceSegment_043_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 351 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 342 9 9, g32p_row25_traceSegment_043_0342_0009, g32p_row25_traceSegment_043_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 324 18 18, g32p_row25_traceSegment_043_0324_0018, g32p_row25_traceSegment_043_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_043 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 288 36 36, g32p_row25_traceSegment_043_0288_0036, g32p_row25_traceSegment_043_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 360 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 360 9 9, g32p_row25_traceSegment_043_0360_0009, g32p_row25_traceSegment_043_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 378 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 387 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 378 9 9, g32p_row25_traceSegment_043_0378_0009, g32p_row25_traceSegment_043_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 360 18 18, g32p_row25_traceSegment_043_0360_0018, g32p_row25_traceSegment_043_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 396 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 405 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 396 9 9, g32p_row25_traceSegment_043_0396_0009, g32p_row25_traceSegment_043_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 414 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 414 9 9, g32p_row25_traceSegment_043_0414_0009, g32p_row25_traceSegment_043_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 396 18 18, g32p_row25_traceSegment_043_0396_0018, g32p_row25_traceSegment_043_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_043 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 360 36 36, g32p_row25_traceSegment_043_0360_0036, g32p_row25_traceSegment_043_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_043 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 288 72 72, g32p_row25_traceSegment_043_0288_0072, g32p_row25_traceSegment_043_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 441 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 432 9 9, g32p_row25_traceSegment_043_0432_0009, g32p_row25_traceSegment_043_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 450 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 450 9 9, g32p_row25_traceSegment_043_0450_0009, g32p_row25_traceSegment_043_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 432 18 18, g32p_row25_traceSegment_043_0432_0018, g32p_row25_traceSegment_043_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 468 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 477 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 468 18 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 468 9 9, g32p_row25_traceSegment_043_0468_0009, g32p_row25_traceSegment_043_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 486 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 495 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 486 18 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 486 9 9, g32p_row25_traceSegment_043_0486_0009, g32p_row25_traceSegment_043_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 468 36 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 468 18 18, g32p_row25_traceSegment_043_0468_0018, g32p_row25_traceSegment_043_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_043 432 72 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 432 36 36, g32p_row25_traceSegment_043_0432_0036, g32p_row25_traceSegment_043_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 504 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 513 9 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 504 18 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 504 9 9, g32p_row25_traceSegment_043_0504_0009, g32p_row25_traceSegment_043_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 531 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 522 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 522 9 9, g32p_row25_traceSegment_043_0522_0009, g32p_row25_traceSegment_043_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 504 36 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 504 18 18, g32p_row25_traceSegment_043_0504_0018, g32p_row25_traceSegment_043_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 540 9 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 540 18 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 540 9 9, g32p_row25_traceSegment_043_0540_0009, g32p_row25_traceSegment_043_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_043 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_043_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_043 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 558 9 9, g32p_row25_traceSegment_043_0558_0009, g32p_row25_traceSegment_043_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_043 540 36 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 540 18 18, g32p_row25_traceSegment_043_0540_0018, g32p_row25_traceSegment_043_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_043 504 72 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 504 36 36, g32p_row25_traceSegment_043_0504_0036, g32p_row25_traceSegment_043_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_043 432 144 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 432 72 72, g32p_row25_traceSegment_043_0432_0072, g32p_row25_traceSegment_043_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_043 288 288 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 288 144 144, g32p_row25_traceSegment_043_0288_0144, g32p_row25_traceSegment_043_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_043_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_043 0 576 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_043 0 288 288, g32p_row25_traceSegment_043_0000_0288, g32p_row25_traceSegment_043_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 43 = [0, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_043_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row25_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 25) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 25) (g32p_literalTraceValue 24 25)
      [1, -1, 1] [0, 0, 1728, 1728] = true := by
  rw [g32p_row25_traceCoefficients_025]
  decide +kernel

theorem g32p_row25_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 29) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 29) (g32p_literalTraceValue 24 29)
      [1, -1, 1] [-1728] = true := by
  rw [g32p_row25_traceCoefficients_029]
  decide +kernel

theorem g32p_row25_tracePolynomial_030 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 30) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 30) (g32p_literalTraceValue 24 30)
      [1, -1, 1] [576, 576, 576] = true := by
  rw [g32p_row25_traceCoefficients_030]
  decide +kernel

theorem g32p_row25_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 31) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 31) (g32p_literalTraceValue 24 31)
      [1, -1, 1] [-3456] = true := by
  rw [g32p_row25_traceCoefficients_031]
  decide +kernel

theorem g32p_row25_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 34) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 34) (g32p_literalTraceValue 24 34)
      [1, -1, 1] [5760, 9216, 9216] = true := by
  rw [g32p_row25_traceCoefficients_034]
  decide +kernel

theorem g32p_row25_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 37) (g32p_literalTraceValue 24 37)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row25_traceCoefficients_037]
  decide +kernel

theorem g32p_row25_tracePolynomial_038 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 38) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 38) (g32p_literalTraceValue 24 38)
      [1, -1, 1] [576, 576] = true := by
  rw [g32p_row25_traceCoefficients_038]
  decide +kernel

theorem g32p_row25_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 43) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 43) (g32p_literalTraceValue 24 43)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row25_traceCoefficients_043]
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

private def g32p_row25_traceSegment_046 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 46 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_046_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 0 9 9, g32p_row25_traceSegment_046_0000_0009, g32p_row25_traceSegment_046_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 18 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 27 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 18 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 18 9 9, g32p_row25_traceSegment_046_0018_0009, g32p_row25_traceSegment_046_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 0 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 0 18 18, g32p_row25_traceSegment_046_0000_0018, g32p_row25_traceSegment_046_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 36 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 36 9 9, g32p_row25_traceSegment_046_0036_0009, g32p_row25_traceSegment_046_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 54 9 9, g32p_row25_traceSegment_046_0054_0009, g32p_row25_traceSegment_046_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 36 18 18, g32p_row25_traceSegment_046_0036_0018, g32p_row25_traceSegment_046_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_046 0 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 0 36 36, g32p_row25_traceSegment_046_0000_0036, g32p_row25_traceSegment_046_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 72 9 9, g32p_row25_traceSegment_046_0072_0009, g32p_row25_traceSegment_046_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 90 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 90 9 9, g32p_row25_traceSegment_046_0090_0009, g32p_row25_traceSegment_046_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 72 18 18, g32p_row25_traceSegment_046_0072_0018, g32p_row25_traceSegment_046_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 108 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 108 9 9, g32p_row25_traceSegment_046_0108_0009, g32p_row25_traceSegment_046_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 126 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 126 9 9, g32p_row25_traceSegment_046_0126_0009, g32p_row25_traceSegment_046_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 108 18 18, g32p_row25_traceSegment_046_0108_0018, g32p_row25_traceSegment_046_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_046 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 72 36 36, g32p_row25_traceSegment_046_0072_0036, g32p_row25_traceSegment_046_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_046 0 144 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 0 72 72, g32p_row25_traceSegment_046_0000_0072, g32p_row25_traceSegment_046_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 144 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 153 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 144 9 9, g32p_row25_traceSegment_046_0144_0009, g32p_row25_traceSegment_046_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 162 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 162 9 9, g32p_row25_traceSegment_046_0162_0009, g32p_row25_traceSegment_046_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 144 18 18, g32p_row25_traceSegment_046_0144_0018, g32p_row25_traceSegment_046_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 180 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 189 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 180 9 9, g32p_row25_traceSegment_046_0180_0009, g32p_row25_traceSegment_046_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 198 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 207 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 198 9 9, g32p_row25_traceSegment_046_0198_0009, g32p_row25_traceSegment_046_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 180 18 18, g32p_row25_traceSegment_046_0180_0018, g32p_row25_traceSegment_046_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_046 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 144 36 36, g32p_row25_traceSegment_046_0144_0036, g32p_row25_traceSegment_046_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 216 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 225 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 216 9 9, g32p_row25_traceSegment_046_0216_0009, g32p_row25_traceSegment_046_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 234 9 9, g32p_row25_traceSegment_046_0234_0009, g32p_row25_traceSegment_046_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 216 18 18, g32p_row25_traceSegment_046_0216_0018, g32p_row25_traceSegment_046_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 252 9 9, g32p_row25_traceSegment_046_0252_0009, g32p_row25_traceSegment_046_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 270 9 9, g32p_row25_traceSegment_046_0270_0009, g32p_row25_traceSegment_046_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 252 18 18, g32p_row25_traceSegment_046_0252_0018, g32p_row25_traceSegment_046_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_046 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 216 36 36, g32p_row25_traceSegment_046_0216_0036, g32p_row25_traceSegment_046_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_046 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 144 72 72, g32p_row25_traceSegment_046_0144_0072, g32p_row25_traceSegment_046_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_046 0 288 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 0 144 144, g32p_row25_traceSegment_046_0000_0144, g32p_row25_traceSegment_046_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 288 9 9, g32p_row25_traceSegment_046_0288_0009, g32p_row25_traceSegment_046_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 306 9 9, g32p_row25_traceSegment_046_0306_0009, g32p_row25_traceSegment_046_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 288 18 18, g32p_row25_traceSegment_046_0288_0018, g32p_row25_traceSegment_046_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 324 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 333 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 324 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 324 9 9, g32p_row25_traceSegment_046_0324_0009, g32p_row25_traceSegment_046_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 342 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 351 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 342 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 342 9 9, g32p_row25_traceSegment_046_0342_0009, g32p_row25_traceSegment_046_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 324 36 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 324 18 18, g32p_row25_traceSegment_046_0324_0018, g32p_row25_traceSegment_046_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_046 288 72 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 288 36 36, g32p_row25_traceSegment_046_0288_0036, g32p_row25_traceSegment_046_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 360 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 369 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 360 18 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 360 9 9, g32p_row25_traceSegment_046_0360_0009, g32p_row25_traceSegment_046_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 378 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 387 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 378 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 378 9 9, g32p_row25_traceSegment_046_0378_0009, g32p_row25_traceSegment_046_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 360 36 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 360 18 18, g32p_row25_traceSegment_046_0360_0018, g32p_row25_traceSegment_046_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 396 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 405 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 396 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 396 9 9, g32p_row25_traceSegment_046_0396_0009, g32p_row25_traceSegment_046_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 414 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 414 9 9, g32p_row25_traceSegment_046_0414_0009, g32p_row25_traceSegment_046_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 396 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 396 18 18, g32p_row25_traceSegment_046_0396_0018, g32p_row25_traceSegment_046_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_046 360 72 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 360 36 36, g32p_row25_traceSegment_046_0360_0036, g32p_row25_traceSegment_046_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_046 288 144 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 288 72 72, g32p_row25_traceSegment_046_0288_0072, g32p_row25_traceSegment_046_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 441 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 432 9 9, g32p_row25_traceSegment_046_0432_0009, g32p_row25_traceSegment_046_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 450 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 450 9 9, g32p_row25_traceSegment_046_0450_0009, g32p_row25_traceSegment_046_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 432 18 18, g32p_row25_traceSegment_046_0432_0018, g32p_row25_traceSegment_046_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 468 9 9, g32p_row25_traceSegment_046_0468_0009, g32p_row25_traceSegment_046_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 486 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 486 9 9, g32p_row25_traceSegment_046_0486_0009, g32p_row25_traceSegment_046_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 468 18 18, g32p_row25_traceSegment_046_0468_0018, g32p_row25_traceSegment_046_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_046 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 432 36 36, g32p_row25_traceSegment_046_0432_0036, g32p_row25_traceSegment_046_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 504 9 9, g32p_row25_traceSegment_046_0504_0009, g32p_row25_traceSegment_046_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 522 9 9, g32p_row25_traceSegment_046_0522_0009, g32p_row25_traceSegment_046_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 504 18 18, g32p_row25_traceSegment_046_0504_0018, g32p_row25_traceSegment_046_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 540 9 9, g32p_row25_traceSegment_046_0540_0009, g32p_row25_traceSegment_046_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_046 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_046_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_046 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 558 9 9, g32p_row25_traceSegment_046_0558_0009, g32p_row25_traceSegment_046_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_046 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 540 18 18, g32p_row25_traceSegment_046_0540_0018, g32p_row25_traceSegment_046_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_046 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 504 36 36, g32p_row25_traceSegment_046_0504_0036, g32p_row25_traceSegment_046_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_046 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 432 72 72, g32p_row25_traceSegment_046_0432_0072, g32p_row25_traceSegment_046_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_046 288 288 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 288 144 144, g32p_row25_traceSegment_046_0288_0144, g32p_row25_traceSegment_046_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_046_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_046 0 576 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_046 0 288 288, g32p_row25_traceSegment_046_0000_0288, g32p_row25_traceSegment_046_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_046 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 46 = [0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_046_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_049 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 49 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_049_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 0 9 9, g32p_row25_traceSegment_049_0000_0009, g32p_row25_traceSegment_049_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 18 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 18 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 18 9 9, g32p_row25_traceSegment_049_0018_0009, g32p_row25_traceSegment_049_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 0 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 0 18 18, g32p_row25_traceSegment_049_0000_0018, g32p_row25_traceSegment_049_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 36 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 45 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 36 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 36 9 9, g32p_row25_traceSegment_049_0036_0009, g32p_row25_traceSegment_049_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 54 9 9, g32p_row25_traceSegment_049_0054_0009, g32p_row25_traceSegment_049_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 36 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 36 18 18, g32p_row25_traceSegment_049_0036_0018, g32p_row25_traceSegment_049_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_049 0 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 0 36 36, g32p_row25_traceSegment_049_0000_0036, g32p_row25_traceSegment_049_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 72 9 9, g32p_row25_traceSegment_049_0072_0009, g32p_row25_traceSegment_049_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 90 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 90 9 9, g32p_row25_traceSegment_049_0090_0009, g32p_row25_traceSegment_049_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 72 18 18, g32p_row25_traceSegment_049_0072_0018, g32p_row25_traceSegment_049_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 108 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 108 9 9, g32p_row25_traceSegment_049_0108_0009, g32p_row25_traceSegment_049_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 126 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 135 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 126 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 126 9 9, g32p_row25_traceSegment_049_0126_0009, g32p_row25_traceSegment_049_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 108 36 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 108 18 18, g32p_row25_traceSegment_049_0108_0018, g32p_row25_traceSegment_049_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_049 72 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 72 36 36, g32p_row25_traceSegment_049_0072_0036, g32p_row25_traceSegment_049_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_049 0 144 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 0 72 72, g32p_row25_traceSegment_049_0000_0072, g32p_row25_traceSegment_049_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 144 9 = [0, 0, 1, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 153 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 144 18 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 144 9 9, g32p_row25_traceSegment_049_0144_0009, g32p_row25_traceSegment_049_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 162 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 171 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 162 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 162 9 9, g32p_row25_traceSegment_049_0162_0009, g32p_row25_traceSegment_049_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 144 36 = [0, 0, 4, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 144 18 18, g32p_row25_traceSegment_049_0144_0018, g32p_row25_traceSegment_049_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 180 9 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 189 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 180 18 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 180 9 9, g32p_row25_traceSegment_049_0180_0009, g32p_row25_traceSegment_049_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 198 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 207 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 198 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 198 9 9, g32p_row25_traceSegment_049_0198_0009, g32p_row25_traceSegment_049_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 180 36 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 180 18 18, g32p_row25_traceSegment_049_0180_0018, g32p_row25_traceSegment_049_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_049 144 72 = [0, 0, 7, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 144 36 36, g32p_row25_traceSegment_049_0144_0036, g32p_row25_traceSegment_049_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 216 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 225 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 216 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 216 9 9, g32p_row25_traceSegment_049_0216_0009, g32p_row25_traceSegment_049_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 234 9 9, g32p_row25_traceSegment_049_0234_0009, g32p_row25_traceSegment_049_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 216 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 216 18 18, g32p_row25_traceSegment_049_0216_0018, g32p_row25_traceSegment_049_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 252 9 9, g32p_row25_traceSegment_049_0252_0009, g32p_row25_traceSegment_049_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 270 9 9, g32p_row25_traceSegment_049_0270_0009, g32p_row25_traceSegment_049_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 252 18 18, g32p_row25_traceSegment_049_0252_0018, g32p_row25_traceSegment_049_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_049 216 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 216 36 36, g32p_row25_traceSegment_049_0216_0036, g32p_row25_traceSegment_049_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_049 144 144 = [0, 0, 8, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 144 72 72, g32p_row25_traceSegment_049_0144_0072, g32p_row25_traceSegment_049_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_049 0 288 = [0, 0, 8, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 0 144 144, g32p_row25_traceSegment_049_0000_0144, g32p_row25_traceSegment_049_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 288 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 297 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 288 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 288 9 9, g32p_row25_traceSegment_049_0288_0009, g32p_row25_traceSegment_049_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 306 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 315 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 306 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 306 9 9, g32p_row25_traceSegment_049_0306_0009, g32p_row25_traceSegment_049_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 288 36 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 288 18 18, g32p_row25_traceSegment_049_0288_0018, g32p_row25_traceSegment_049_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 324 9 = [0, 0, 2, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 333 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 324 18 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 324 9 9, g32p_row25_traceSegment_049_0324_0009, g32p_row25_traceSegment_049_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 342 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 351 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 342 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 342 9 9, g32p_row25_traceSegment_049_0342_0009, g32p_row25_traceSegment_049_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 324 36 = [0, 0, 5, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 324 18 18, g32p_row25_traceSegment_049_0324_0018, g32p_row25_traceSegment_049_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_049 288 72 = [0, 0, 6, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 288 36 36, g32p_row25_traceSegment_049_0288_0036, g32p_row25_traceSegment_049_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 360 9 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 369 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 360 18 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 360 9 9, g32p_row25_traceSegment_049_0360_0009, g32p_row25_traceSegment_049_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 378 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 387 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 378 18 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 378 9 9, g32p_row25_traceSegment_049_0378_0009, g32p_row25_traceSegment_049_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 360 36 = [0, 0, 7, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 360 18 18, g32p_row25_traceSegment_049_0360_0018, g32p_row25_traceSegment_049_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 396 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 405 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 396 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 396 9 9, g32p_row25_traceSegment_049_0396_0009, g32p_row25_traceSegment_049_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 414 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 414 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 414 9 9, g32p_row25_traceSegment_049_0414_0009, g32p_row25_traceSegment_049_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 396 36 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 396 18 18, g32p_row25_traceSegment_049_0396_0018, g32p_row25_traceSegment_049_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_049 360 72 = [0, 0, 8, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 360 36 36, g32p_row25_traceSegment_049_0360_0036, g32p_row25_traceSegment_049_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_049 288 144 = [0, 0, 14, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 288 72 72, g32p_row25_traceSegment_049_0288_0072, g32p_row25_traceSegment_049_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 432 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 441 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 432 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 432 9 9, g32p_row25_traceSegment_049_0432_0009, g32p_row25_traceSegment_049_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 450 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 450 9 9, g32p_row25_traceSegment_049_0450_0009, g32p_row25_traceSegment_049_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 432 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 432 18 18, g32p_row25_traceSegment_049_0432_0018, g32p_row25_traceSegment_049_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 468 9 9, g32p_row25_traceSegment_049_0468_0009, g32p_row25_traceSegment_049_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 486 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 495 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 486 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 486 9 9, g32p_row25_traceSegment_049_0486_0009, g32p_row25_traceSegment_049_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 468 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 468 18 18, g32p_row25_traceSegment_049_0468_0018, g32p_row25_traceSegment_049_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_049 432 72 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 432 36 36, g32p_row25_traceSegment_049_0432_0036, g32p_row25_traceSegment_049_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 513 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 504 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 504 9 9, g32p_row25_traceSegment_049_0504_0009, g32p_row25_traceSegment_049_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 522 9 9, g32p_row25_traceSegment_049_0522_0009, g32p_row25_traceSegment_049_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 504 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 504 18 18, g32p_row25_traceSegment_049_0504_0018, g32p_row25_traceSegment_049_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 540 9 9, g32p_row25_traceSegment_049_0540_0009, g32p_row25_traceSegment_049_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_049 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_049_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_049 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 558 9 9, g32p_row25_traceSegment_049_0558_0009, g32p_row25_traceSegment_049_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_049 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 540 18 18, g32p_row25_traceSegment_049_0540_0018, g32p_row25_traceSegment_049_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_049 504 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 504 36 36, g32p_row25_traceSegment_049_0504_0036, g32p_row25_traceSegment_049_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_049 432 144 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 432 72 72, g32p_row25_traceSegment_049_0432_0072, g32p_row25_traceSegment_049_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_049 288 288 = [0, 0, 16, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 288 144 144, g32p_row25_traceSegment_049_0288_0144, g32p_row25_traceSegment_049_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_049_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_049 0 576 = [0, 0, 24, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_049 0 288 288, g32p_row25_traceSegment_049_0000_0288, g32p_row25_traceSegment_049_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_049 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 49 = [0, 0, 24, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_049_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_050 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 50 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_050_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 0 9 9, g32p_row25_traceSegment_050_0000_0009, g32p_row25_traceSegment_050_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 18 9 9, g32p_row25_traceSegment_050_0018_0009, g32p_row25_traceSegment_050_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 0 18 18, g32p_row25_traceSegment_050_0000_0018, g32p_row25_traceSegment_050_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 36 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 45 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 36 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 36 9 9, g32p_row25_traceSegment_050_0036_0009, g32p_row25_traceSegment_050_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 54 9 9, g32p_row25_traceSegment_050_0054_0009, g32p_row25_traceSegment_050_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 36 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 36 18 18, g32p_row25_traceSegment_050_0036_0018, g32p_row25_traceSegment_050_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_050 0 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 0 36 36, g32p_row25_traceSegment_050_0000_0036, g32p_row25_traceSegment_050_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 72 9 9, g32p_row25_traceSegment_050_0072_0009, g32p_row25_traceSegment_050_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 90 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 90 9 9, g32p_row25_traceSegment_050_0090_0009, g32p_row25_traceSegment_050_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 72 18 18, g32p_row25_traceSegment_050_0072_0018, g32p_row25_traceSegment_050_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 108 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 108 9 9, g32p_row25_traceSegment_050_0108_0009, g32p_row25_traceSegment_050_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 126 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 126 9 9, g32p_row25_traceSegment_050_0126_0009, g32p_row25_traceSegment_050_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 108 18 18, g32p_row25_traceSegment_050_0108_0018, g32p_row25_traceSegment_050_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_050 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 72 36 36, g32p_row25_traceSegment_050_0072_0036, g32p_row25_traceSegment_050_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_050 0 144 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 0 72 72, g32p_row25_traceSegment_050_0000_0072, g32p_row25_traceSegment_050_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 144 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 153 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 144 9 9, g32p_row25_traceSegment_050_0144_0009, g32p_row25_traceSegment_050_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 162 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 162 9 9, g32p_row25_traceSegment_050_0162_0009, g32p_row25_traceSegment_050_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 144 18 18, g32p_row25_traceSegment_050_0144_0018, g32p_row25_traceSegment_050_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 180 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 189 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 180 9 9, g32p_row25_traceSegment_050_0180_0009, g32p_row25_traceSegment_050_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 198 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 207 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 198 9 9, g32p_row25_traceSegment_050_0198_0009, g32p_row25_traceSegment_050_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 180 18 18, g32p_row25_traceSegment_050_0180_0018, g32p_row25_traceSegment_050_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_050 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 144 36 36, g32p_row25_traceSegment_050_0144_0036, g32p_row25_traceSegment_050_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 216 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 225 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 216 9 9, g32p_row25_traceSegment_050_0216_0009, g32p_row25_traceSegment_050_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 234 9 9, g32p_row25_traceSegment_050_0234_0009, g32p_row25_traceSegment_050_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 216 18 18, g32p_row25_traceSegment_050_0216_0018, g32p_row25_traceSegment_050_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 252 9 9, g32p_row25_traceSegment_050_0252_0009, g32p_row25_traceSegment_050_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 270 9 9, g32p_row25_traceSegment_050_0270_0009, g32p_row25_traceSegment_050_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 252 18 18, g32p_row25_traceSegment_050_0252_0018, g32p_row25_traceSegment_050_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_050 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 216 36 36, g32p_row25_traceSegment_050_0216_0036, g32p_row25_traceSegment_050_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_050 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 144 72 72, g32p_row25_traceSegment_050_0144_0072, g32p_row25_traceSegment_050_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_050 0 288 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 0 144 144, g32p_row25_traceSegment_050_0000_0144, g32p_row25_traceSegment_050_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 297 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 288 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 288 9 9, g32p_row25_traceSegment_050_0288_0009, g32p_row25_traceSegment_050_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 315 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 306 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 306 9 9, g32p_row25_traceSegment_050_0306_0009, g32p_row25_traceSegment_050_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 288 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 288 18 18, g32p_row25_traceSegment_050_0288_0018, g32p_row25_traceSegment_050_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 333 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 324 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 324 9 9, g32p_row25_traceSegment_050_0324_0009, g32p_row25_traceSegment_050_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 351 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 342 9 9, g32p_row25_traceSegment_050_0342_0009, g32p_row25_traceSegment_050_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 324 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 324 18 18, g32p_row25_traceSegment_050_0324_0018, g32p_row25_traceSegment_050_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_050 288 72 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 288 36 36, g32p_row25_traceSegment_050_0288_0036, g32p_row25_traceSegment_050_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 360 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 369 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 360 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 360 9 9, g32p_row25_traceSegment_050_0360_0009, g32p_row25_traceSegment_050_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 378 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 387 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 378 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 378 9 9, g32p_row25_traceSegment_050_0378_0009, g32p_row25_traceSegment_050_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 360 36 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 360 18 18, g32p_row25_traceSegment_050_0360_0018, g32p_row25_traceSegment_050_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 396 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 405 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 396 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 396 9 9, g32p_row25_traceSegment_050_0396_0009, g32p_row25_traceSegment_050_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 414 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 423 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 414 18 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 414 9 9, g32p_row25_traceSegment_050_0414_0009, g32p_row25_traceSegment_050_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 396 36 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 396 18 18, g32p_row25_traceSegment_050_0396_0018, g32p_row25_traceSegment_050_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_050 360 72 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 360 36 36, g32p_row25_traceSegment_050_0360_0036, g32p_row25_traceSegment_050_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_050 288 144 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 288 72 72, g32p_row25_traceSegment_050_0288_0072, g32p_row25_traceSegment_050_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 441 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 432 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 432 9 9, g32p_row25_traceSegment_050_0432_0009, g32p_row25_traceSegment_050_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 450 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 450 9 9, g32p_row25_traceSegment_050_0450_0009, g32p_row25_traceSegment_050_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 432 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 432 18 18, g32p_row25_traceSegment_050_0432_0018, g32p_row25_traceSegment_050_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 468 9 9, g32p_row25_traceSegment_050_0468_0009, g32p_row25_traceSegment_050_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 486 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 486 9 9, g32p_row25_traceSegment_050_0486_0009, g32p_row25_traceSegment_050_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 468 18 18, g32p_row25_traceSegment_050_0468_0018, g32p_row25_traceSegment_050_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_050 432 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 432 36 36, g32p_row25_traceSegment_050_0432_0036, g32p_row25_traceSegment_050_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 504 9 9, g32p_row25_traceSegment_050_0504_0009, g32p_row25_traceSegment_050_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 531 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 522 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 522 9 9, g32p_row25_traceSegment_050_0522_0009, g32p_row25_traceSegment_050_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 504 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 504 18 18, g32p_row25_traceSegment_050_0504_0018, g32p_row25_traceSegment_050_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 540 9 9, g32p_row25_traceSegment_050_0540_0009, g32p_row25_traceSegment_050_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_050 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_050_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_050 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 558 9 9, g32p_row25_traceSegment_050_0558_0009, g32p_row25_traceSegment_050_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_050 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 540 18 18, g32p_row25_traceSegment_050_0540_0018, g32p_row25_traceSegment_050_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_050 504 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 504 36 36, g32p_row25_traceSegment_050_0504_0036, g32p_row25_traceSegment_050_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_050 432 144 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 432 72 72, g32p_row25_traceSegment_050_0432_0072, g32p_row25_traceSegment_050_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_050 288 288 = [0, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 288 144 144, g32p_row25_traceSegment_050_0288_0144, g32p_row25_traceSegment_050_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_050_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_050 0 576 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_050 0 288 288, g32p_row25_traceSegment_050_0000_0288, g32p_row25_traceSegment_050_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 50 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_050_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_052 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 52 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_052_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 0 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 9 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 0 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 0 9 9, g32p_row25_traceSegment_052_0000_0009, g32p_row25_traceSegment_052_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 18 9 9, g32p_row25_traceSegment_052_0018_0009, g32p_row25_traceSegment_052_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 0 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 0 18 18, g32p_row25_traceSegment_052_0000_0018, g32p_row25_traceSegment_052_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 36 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 36 9 9, g32p_row25_traceSegment_052_0036_0009, g32p_row25_traceSegment_052_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 54 9 9, g32p_row25_traceSegment_052_0054_0009, g32p_row25_traceSegment_052_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 36 18 18, g32p_row25_traceSegment_052_0036_0018, g32p_row25_traceSegment_052_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_052 0 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 0 36 36, g32p_row25_traceSegment_052_0000_0036, g32p_row25_traceSegment_052_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 72 9 9, g32p_row25_traceSegment_052_0072_0009, g32p_row25_traceSegment_052_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 90 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 90 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 90 9 9, g32p_row25_traceSegment_052_0090_0009, g32p_row25_traceSegment_052_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 72 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 72 18 18, g32p_row25_traceSegment_052_0072_0018, g32p_row25_traceSegment_052_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 108 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 108 9 9, g32p_row25_traceSegment_052_0108_0009, g32p_row25_traceSegment_052_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 126 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 126 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 126 9 9, g32p_row25_traceSegment_052_0126_0009, g32p_row25_traceSegment_052_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 108 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 108 18 18, g32p_row25_traceSegment_052_0108_0018, g32p_row25_traceSegment_052_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_052 72 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 72 36 36, g32p_row25_traceSegment_052_0072_0036, g32p_row25_traceSegment_052_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_052 0 144 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 0 72 72, g32p_row25_traceSegment_052_0000_0072, g32p_row25_traceSegment_052_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 144 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 153 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 144 9 9, g32p_row25_traceSegment_052_0144_0009, g32p_row25_traceSegment_052_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 162 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 162 9 9, g32p_row25_traceSegment_052_0162_0009, g32p_row25_traceSegment_052_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 144 18 18, g32p_row25_traceSegment_052_0144_0018, g32p_row25_traceSegment_052_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 180 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 189 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 180 9 9, g32p_row25_traceSegment_052_0180_0009, g32p_row25_traceSegment_052_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 198 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 207 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 198 9 9, g32p_row25_traceSegment_052_0198_0009, g32p_row25_traceSegment_052_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 180 18 18, g32p_row25_traceSegment_052_0180_0018, g32p_row25_traceSegment_052_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_052 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 144 36 36, g32p_row25_traceSegment_052_0144_0036, g32p_row25_traceSegment_052_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 216 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 225 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 216 9 9, g32p_row25_traceSegment_052_0216_0009, g32p_row25_traceSegment_052_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 234 9 9, g32p_row25_traceSegment_052_0234_0009, g32p_row25_traceSegment_052_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 216 18 18, g32p_row25_traceSegment_052_0216_0018, g32p_row25_traceSegment_052_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 252 9 9, g32p_row25_traceSegment_052_0252_0009, g32p_row25_traceSegment_052_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 270 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 279 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 270 18 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 270 9 9, g32p_row25_traceSegment_052_0270_0009, g32p_row25_traceSegment_052_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 252 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 252 18 18, g32p_row25_traceSegment_052_0252_0018, g32p_row25_traceSegment_052_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_052 216 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 216 36 36, g32p_row25_traceSegment_052_0216_0036, g32p_row25_traceSegment_052_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_052 144 144 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 144 72 72, g32p_row25_traceSegment_052_0144_0072, g32p_row25_traceSegment_052_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_052 0 288 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 0 144 144, g32p_row25_traceSegment_052_0000_0144, g32p_row25_traceSegment_052_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 288 9 9, g32p_row25_traceSegment_052_0288_0009, g32p_row25_traceSegment_052_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 306 9 9, g32p_row25_traceSegment_052_0306_0009, g32p_row25_traceSegment_052_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 288 18 18, g32p_row25_traceSegment_052_0288_0018, g32p_row25_traceSegment_052_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 333 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 324 9 9, g32p_row25_traceSegment_052_0324_0009, g32p_row25_traceSegment_052_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 351 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 342 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 342 9 9, g32p_row25_traceSegment_052_0342_0009, g32p_row25_traceSegment_052_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 324 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 324 18 18, g32p_row25_traceSegment_052_0324_0018, g32p_row25_traceSegment_052_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_052 288 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 288 36 36, g32p_row25_traceSegment_052_0288_0036, g32p_row25_traceSegment_052_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 360 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 360 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 360 9 9, g32p_row25_traceSegment_052_0360_0009, g32p_row25_traceSegment_052_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 378 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 387 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 378 9 9, g32p_row25_traceSegment_052_0378_0009, g32p_row25_traceSegment_052_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 360 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 360 18 18, g32p_row25_traceSegment_052_0360_0018, g32p_row25_traceSegment_052_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 396 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 405 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 396 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 396 9 9, g32p_row25_traceSegment_052_0396_0009, g32p_row25_traceSegment_052_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 414 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 414 9 9, g32p_row25_traceSegment_052_0414_0009, g32p_row25_traceSegment_052_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 396 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 396 18 18, g32p_row25_traceSegment_052_0396_0018, g32p_row25_traceSegment_052_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_052 360 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 360 36 36, g32p_row25_traceSegment_052_0360_0036, g32p_row25_traceSegment_052_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_052 288 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 288 72 72, g32p_row25_traceSegment_052_0288_0072, g32p_row25_traceSegment_052_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 441 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 432 9 9, g32p_row25_traceSegment_052_0432_0009, g32p_row25_traceSegment_052_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 450 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 450 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 450 9 9, g32p_row25_traceSegment_052_0450_0009, g32p_row25_traceSegment_052_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 432 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 432 18 18, g32p_row25_traceSegment_052_0432_0018, g32p_row25_traceSegment_052_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 468 9 9, g32p_row25_traceSegment_052_0468_0009, g32p_row25_traceSegment_052_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 486 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 486 9 9, g32p_row25_traceSegment_052_0486_0009, g32p_row25_traceSegment_052_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 468 18 18, g32p_row25_traceSegment_052_0468_0018, g32p_row25_traceSegment_052_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_052 432 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 432 36 36, g32p_row25_traceSegment_052_0432_0036, g32p_row25_traceSegment_052_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 513 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 504 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 504 9 9, g32p_row25_traceSegment_052_0504_0009, g32p_row25_traceSegment_052_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 522 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 522 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 522 9 9, g32p_row25_traceSegment_052_0522_0009, g32p_row25_traceSegment_052_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 504 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 504 18 18, g32p_row25_traceSegment_052_0504_0018, g32p_row25_traceSegment_052_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 540 9 9, g32p_row25_traceSegment_052_0540_0009, g32p_row25_traceSegment_052_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_052 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_052_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_052 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 558 9 9, g32p_row25_traceSegment_052_0558_0009, g32p_row25_traceSegment_052_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_052 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 540 18 18, g32p_row25_traceSegment_052_0540_0018, g32p_row25_traceSegment_052_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_052 504 72 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 504 36 36, g32p_row25_traceSegment_052_0504_0036, g32p_row25_traceSegment_052_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_052 432 144 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 432 72 72, g32p_row25_traceSegment_052_0432_0072, g32p_row25_traceSegment_052_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_052 288 288 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 288 144 144, g32p_row25_traceSegment_052_0288_0144, g32p_row25_traceSegment_052_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_052_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_052 0 576 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_052 0 288 288, g32p_row25_traceSegment_052_0000_0288, g32p_row25_traceSegment_052_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 52 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_052_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_056 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 56 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_056_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 0 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 9 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 0 9 9, g32p_row25_traceSegment_056_0000_0009, g32p_row25_traceSegment_056_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 18 9 9, g32p_row25_traceSegment_056_0018_0009, g32p_row25_traceSegment_056_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 0 18 18, g32p_row25_traceSegment_056_0000_0018, g32p_row25_traceSegment_056_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 36 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 36 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 36 9 9, g32p_row25_traceSegment_056_0036_0009, g32p_row25_traceSegment_056_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 54 9 9, g32p_row25_traceSegment_056_0054_0009, g32p_row25_traceSegment_056_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 36 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 36 18 18, g32p_row25_traceSegment_056_0036_0018, g32p_row25_traceSegment_056_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_056 0 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 0 36 36, g32p_row25_traceSegment_056_0000_0036, g32p_row25_traceSegment_056_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 72 9 9, g32p_row25_traceSegment_056_0072_0009, g32p_row25_traceSegment_056_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 90 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 99 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 90 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 90 9 9, g32p_row25_traceSegment_056_0090_0009, g32p_row25_traceSegment_056_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 72 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 72 18 18, g32p_row25_traceSegment_056_0072_0018, g32p_row25_traceSegment_056_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 108 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 108 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 108 9 9, g32p_row25_traceSegment_056_0108_0009, g32p_row25_traceSegment_056_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 126 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 126 9 9, g32p_row25_traceSegment_056_0126_0009, g32p_row25_traceSegment_056_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 108 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 108 18 18, g32p_row25_traceSegment_056_0108_0018, g32p_row25_traceSegment_056_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_056 72 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 72 36 36, g32p_row25_traceSegment_056_0072_0036, g32p_row25_traceSegment_056_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_056 0 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 0 72 72, g32p_row25_traceSegment_056_0000_0072, g32p_row25_traceSegment_056_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 144 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 153 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 144 9 9, g32p_row25_traceSegment_056_0144_0009, g32p_row25_traceSegment_056_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 162 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 162 9 9, g32p_row25_traceSegment_056_0162_0009, g32p_row25_traceSegment_056_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 144 18 18, g32p_row25_traceSegment_056_0144_0018, g32p_row25_traceSegment_056_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 180 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 189 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 180 9 9, g32p_row25_traceSegment_056_0180_0009, g32p_row25_traceSegment_056_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 198 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 207 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 198 9 9, g32p_row25_traceSegment_056_0198_0009, g32p_row25_traceSegment_056_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 180 18 18, g32p_row25_traceSegment_056_0180_0018, g32p_row25_traceSegment_056_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_056 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 144 36 36, g32p_row25_traceSegment_056_0144_0036, g32p_row25_traceSegment_056_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 216 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 225 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 216 9 9, g32p_row25_traceSegment_056_0216_0009, g32p_row25_traceSegment_056_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 234 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 243 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 234 9 9, g32p_row25_traceSegment_056_0234_0009, g32p_row25_traceSegment_056_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 216 18 18, g32p_row25_traceSegment_056_0216_0018, g32p_row25_traceSegment_056_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 252 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 252 9 9, g32p_row25_traceSegment_056_0252_0009, g32p_row25_traceSegment_056_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 270 9 9, g32p_row25_traceSegment_056_0270_0009, g32p_row25_traceSegment_056_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 252 18 18, g32p_row25_traceSegment_056_0252_0018, g32p_row25_traceSegment_056_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_056 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 216 36 36, g32p_row25_traceSegment_056_0216_0036, g32p_row25_traceSegment_056_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_056 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 144 72 72, g32p_row25_traceSegment_056_0144_0072, g32p_row25_traceSegment_056_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_056 0 288 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 0 144 144, g32p_row25_traceSegment_056_0000_0144, g32p_row25_traceSegment_056_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 288 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 297 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 288 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 288 9 9, g32p_row25_traceSegment_056_0288_0009, g32p_row25_traceSegment_056_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 306 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 306 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 306 9 9, g32p_row25_traceSegment_056_0306_0009, g32p_row25_traceSegment_056_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 288 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 288 18 18, g32p_row25_traceSegment_056_0288_0018, g32p_row25_traceSegment_056_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 333 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 324 9 9, g32p_row25_traceSegment_056_0324_0009, g32p_row25_traceSegment_056_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 351 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 342 9 9, g32p_row25_traceSegment_056_0342_0009, g32p_row25_traceSegment_056_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 324 18 18, g32p_row25_traceSegment_056_0324_0018, g32p_row25_traceSegment_056_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_056 288 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 288 36 36, g32p_row25_traceSegment_056_0288_0036, g32p_row25_traceSegment_056_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 360 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 360 9 9, g32p_row25_traceSegment_056_0360_0009, g32p_row25_traceSegment_056_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 378 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 387 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 378 9 9, g32p_row25_traceSegment_056_0378_0009, g32p_row25_traceSegment_056_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 360 18 18, g32p_row25_traceSegment_056_0360_0018, g32p_row25_traceSegment_056_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 396 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 405 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 396 9 9, g32p_row25_traceSegment_056_0396_0009, g32p_row25_traceSegment_056_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 414 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 423 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 414 9 9, g32p_row25_traceSegment_056_0414_0009, g32p_row25_traceSegment_056_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 396 18 18, g32p_row25_traceSegment_056_0396_0018, g32p_row25_traceSegment_056_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_056 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 360 36 36, g32p_row25_traceSegment_056_0360_0036, g32p_row25_traceSegment_056_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_056 288 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 288 72 72, g32p_row25_traceSegment_056_0288_0072, g32p_row25_traceSegment_056_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 432 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 441 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 432 9 9, g32p_row25_traceSegment_056_0432_0009, g32p_row25_traceSegment_056_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 450 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 459 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 450 9 9, g32p_row25_traceSegment_056_0450_0009, g32p_row25_traceSegment_056_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 432 18 18, g32p_row25_traceSegment_056_0432_0018, g32p_row25_traceSegment_056_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 468 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 477 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 468 9 9, g32p_row25_traceSegment_056_0468_0009, g32p_row25_traceSegment_056_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 486 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 486 9 9, g32p_row25_traceSegment_056_0486_0009, g32p_row25_traceSegment_056_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 468 18 18, g32p_row25_traceSegment_056_0468_0018, g32p_row25_traceSegment_056_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_056 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 432 36 36, g32p_row25_traceSegment_056_0432_0036, g32p_row25_traceSegment_056_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 504 9 9, g32p_row25_traceSegment_056_0504_0009, g32p_row25_traceSegment_056_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 522 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 522 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 522 9 9, g32p_row25_traceSegment_056_0522_0009, g32p_row25_traceSegment_056_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 504 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 504 18 18, g32p_row25_traceSegment_056_0504_0018, g32p_row25_traceSegment_056_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 549 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 540 9 9, g32p_row25_traceSegment_056_0540_0009, g32p_row25_traceSegment_056_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 558 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_056 567 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_056_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_056 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 558 9 9, g32p_row25_traceSegment_056_0558_0009, g32p_row25_traceSegment_056_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_056 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 540 18 18, g32p_row25_traceSegment_056_0540_0018, g32p_row25_traceSegment_056_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_056 504 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 504 36 36, g32p_row25_traceSegment_056_0504_0036, g32p_row25_traceSegment_056_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_056 432 144 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 432 72 72, g32p_row25_traceSegment_056_0432_0072, g32p_row25_traceSegment_056_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_056 288 288 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 288 144 144, g32p_row25_traceSegment_056_0288_0144, g32p_row25_traceSegment_056_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_056_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_056 0 576 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_056 0 288 288, g32p_row25_traceSegment_056_0000_0288, g32p_row25_traceSegment_056_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 56 = [0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_056_0000_0576

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row25_traceSegment_057 (k : ℕ) : List ℤ :=
  if g32p_row25_supplierClassifier (Fin.ofNat 576 k) = 57 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row25_characterValues (Fin.ofNat 576 k))).val 1 else []

private theorem g32p_row25_traceSegment_057_0000_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 0 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0009_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 9 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0000_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 0 18 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 0 9 9, g32p_row25_traceSegment_057_0000_0009, g32p_row25_traceSegment_057_0009_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0018_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 18 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0027_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 27 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0018_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 18 9 9, g32p_row25_traceSegment_057_0018_0009, g32p_row25_traceSegment_057_0027_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0000_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 0 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 0 18 18, g32p_row25_traceSegment_057_0000_0018, g32p_row25_traceSegment_057_0018_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0036_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 36 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0045_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 45 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0036_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 36 9 9, g32p_row25_traceSegment_057_0036_0009, g32p_row25_traceSegment_057_0045_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0054_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 54 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0063_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 63 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0054_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 54 9 9, g32p_row25_traceSegment_057_0054_0009, g32p_row25_traceSegment_057_0063_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0036_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 36 18 18, g32p_row25_traceSegment_057_0036_0018, g32p_row25_traceSegment_057_0054_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0000_0072 : g32p_coeffSegment g32p_row25_traceSegment_057 0 72 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 0 36 36, g32p_row25_traceSegment_057_0000_0036, g32p_row25_traceSegment_057_0036_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0072_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 72 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0081_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 81 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0072_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 72 9 9, g32p_row25_traceSegment_057_0072_0009, g32p_row25_traceSegment_057_0081_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0090_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 90 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0099_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 99 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0090_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 90 9 9, g32p_row25_traceSegment_057_0090_0009, g32p_row25_traceSegment_057_0099_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0072_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 72 18 18, g32p_row25_traceSegment_057_0072_0018, g32p_row25_traceSegment_057_0090_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0108_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 108 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0117_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 117 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0108_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 108 9 9, g32p_row25_traceSegment_057_0108_0009, g32p_row25_traceSegment_057_0117_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0126_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 126 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0135_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 135 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0126_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 126 9 9, g32p_row25_traceSegment_057_0126_0009, g32p_row25_traceSegment_057_0135_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0108_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 108 18 18, g32p_row25_traceSegment_057_0108_0018, g32p_row25_traceSegment_057_0126_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0072_0072 : g32p_coeffSegment g32p_row25_traceSegment_057 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 72 36 36, g32p_row25_traceSegment_057_0072_0036, g32p_row25_traceSegment_057_0108_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0000_0144 : g32p_coeffSegment g32p_row25_traceSegment_057 0 144 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 0 72 72, g32p_row25_traceSegment_057_0000_0072, g32p_row25_traceSegment_057_0072_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0144_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 144 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0153_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 153 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0144_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 144 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 144 9 9, g32p_row25_traceSegment_057_0144_0009, g32p_row25_traceSegment_057_0153_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0162_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 162 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0171_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 171 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0162_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 162 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 162 9 9, g32p_row25_traceSegment_057_0162_0009, g32p_row25_traceSegment_057_0171_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0144_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 144 36 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 144 18 18, g32p_row25_traceSegment_057_0144_0018, g32p_row25_traceSegment_057_0162_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0180_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 180 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0189_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 189 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0180_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 180 18 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 180 9 9, g32p_row25_traceSegment_057_0180_0009, g32p_row25_traceSegment_057_0189_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0198_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 198 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0207_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 207 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0198_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 198 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 198 9 9, g32p_row25_traceSegment_057_0198_0009, g32p_row25_traceSegment_057_0207_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0180_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 180 36 = [0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 180 18 18, g32p_row25_traceSegment_057_0180_0018, g32p_row25_traceSegment_057_0198_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0144_0072 : g32p_coeffSegment g32p_row25_traceSegment_057 144 72 = [0, 6, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 144 36 36, g32p_row25_traceSegment_057_0144_0036, g32p_row25_traceSegment_057_0180_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0216_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 216 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0225_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 225 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0216_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 216 18 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 216 9 9, g32p_row25_traceSegment_057_0216_0009, g32p_row25_traceSegment_057_0225_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0234_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 234 9 = [0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0243_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 243 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0234_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 234 18 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 234 9 9, g32p_row25_traceSegment_057_0234_0009, g32p_row25_traceSegment_057_0243_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0216_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 216 36 = [0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 216 18 18, g32p_row25_traceSegment_057_0216_0018, g32p_row25_traceSegment_057_0234_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0252_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 252 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0261_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 261 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0252_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 252 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 252 9 9, g32p_row25_traceSegment_057_0252_0009, g32p_row25_traceSegment_057_0261_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0270_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 270 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0279_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 279 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0270_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 270 9 9, g32p_row25_traceSegment_057_0270_0009, g32p_row25_traceSegment_057_0279_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0252_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 252 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 252 18 18, g32p_row25_traceSegment_057_0252_0018, g32p_row25_traceSegment_057_0270_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0216_0072 : g32p_coeffSegment g32p_row25_traceSegment_057 216 72 = [0, 3, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 216 36 36, g32p_row25_traceSegment_057_0216_0036, g32p_row25_traceSegment_057_0252_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0144_0144 : g32p_coeffSegment g32p_row25_traceSegment_057 144 144 = [0, 9, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 144 72 72, g32p_row25_traceSegment_057_0144_0072, g32p_row25_traceSegment_057_0216_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0000_0288 : g32p_coeffSegment g32p_row25_traceSegment_057 0 288 = [0, 12, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 0 144 144, g32p_row25_traceSegment_057_0000_0144, g32p_row25_traceSegment_057_0144_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0288_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 288 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0297_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 297 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0288_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 288 9 9, g32p_row25_traceSegment_057_0288_0009, g32p_row25_traceSegment_057_0297_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0306_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 306 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0315_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 315 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0306_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 306 9 9, g32p_row25_traceSegment_057_0306_0009, g32p_row25_traceSegment_057_0315_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0288_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 288 18 18, g32p_row25_traceSegment_057_0288_0018, g32p_row25_traceSegment_057_0306_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0324_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 324 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0333_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 333 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0324_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 324 9 9, g32p_row25_traceSegment_057_0324_0009, g32p_row25_traceSegment_057_0333_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0342_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 342 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0351_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 351 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0342_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 342 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 342 9 9, g32p_row25_traceSegment_057_0342_0009, g32p_row25_traceSegment_057_0351_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0324_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 324 36 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 324 18 18, g32p_row25_traceSegment_057_0324_0018, g32p_row25_traceSegment_057_0342_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0288_0072 : g32p_coeffSegment g32p_row25_traceSegment_057 288 72 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 288 36 36, g32p_row25_traceSegment_057_0288_0036, g32p_row25_traceSegment_057_0324_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0360_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 360 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0369_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 369 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0360_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 360 9 9, g32p_row25_traceSegment_057_0360_0009, g32p_row25_traceSegment_057_0369_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0378_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 378 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0387_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 387 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0378_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 378 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 378 9 9, g32p_row25_traceSegment_057_0378_0009, g32p_row25_traceSegment_057_0387_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0360_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 360 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 360 18 18, g32p_row25_traceSegment_057_0360_0018, g32p_row25_traceSegment_057_0378_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0396_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 396 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0405_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 405 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0396_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 396 18 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 396 9 9, g32p_row25_traceSegment_057_0396_0009, g32p_row25_traceSegment_057_0405_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0414_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 414 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0423_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 423 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0414_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 414 18 = [0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 414 9 9, g32p_row25_traceSegment_057_0414_0009, g32p_row25_traceSegment_057_0423_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0396_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 396 36 = [0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 396 18 18, g32p_row25_traceSegment_057_0396_0018, g32p_row25_traceSegment_057_0414_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0360_0072 : g32p_coeffSegment g32p_row25_traceSegment_057 360 72 = [0, 3, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 360 36 36, g32p_row25_traceSegment_057_0360_0036, g32p_row25_traceSegment_057_0396_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0288_0144 : g32p_coeffSegment g32p_row25_traceSegment_057 288 144 = [0, 4, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 288 72 72, g32p_row25_traceSegment_057_0288_0072, g32p_row25_traceSegment_057_0360_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0432_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 432 9 = [0, 1, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0441_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 441 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0432_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 432 18 = [0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 432 9 9, g32p_row25_traceSegment_057_0432_0009, g32p_row25_traceSegment_057_0441_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0450_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 450 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0459_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 459 9 = [0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0450_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 450 18 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 450 9 9, g32p_row25_traceSegment_057_0450_0009, g32p_row25_traceSegment_057_0459_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0432_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 432 36 = [0, 3, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 432 18 18, g32p_row25_traceSegment_057_0432_0018, g32p_row25_traceSegment_057_0450_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0468_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 468 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0477_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 477 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0468_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 468 18 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 468 9 9, g32p_row25_traceSegment_057_0468_0009, g32p_row25_traceSegment_057_0477_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0486_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 486 9 = [0, 1] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0495_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 495 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0486_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 486 18 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 486 9 9, g32p_row25_traceSegment_057_0486_0009, g32p_row25_traceSegment_057_0495_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0468_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 468 36 = [0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 468 18 18, g32p_row25_traceSegment_057_0468_0018, g32p_row25_traceSegment_057_0486_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0432_0072 : g32p_coeffSegment g32p_row25_traceSegment_057 432 72 = [0, 4, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 432 36 36, g32p_row25_traceSegment_057_0432_0036, g32p_row25_traceSegment_057_0468_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0504_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 504 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0513_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 513 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0504_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 504 9 9, g32p_row25_traceSegment_057_0504_0009, g32p_row25_traceSegment_057_0513_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0522_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 522 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0531_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 531 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0522_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 522 9 9, g32p_row25_traceSegment_057_0522_0009, g32p_row25_traceSegment_057_0531_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0504_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 504 18 18, g32p_row25_traceSegment_057_0504_0018, g32p_row25_traceSegment_057_0522_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0540_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 540 9 = [] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0549_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 549 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0540_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 540 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 540 9 9, g32p_row25_traceSegment_057_0540_0009, g32p_row25_traceSegment_057_0549_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0558_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 558 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0567_0009 : g32p_coeffSegment g32p_row25_traceSegment_057 567 9 = [0, 2] := by
  decide +kernel

private theorem g32p_row25_traceSegment_057_0558_0018 : g32p_coeffSegment g32p_row25_traceSegment_057 558 18 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 558 9 9, g32p_row25_traceSegment_057_0558_0009, g32p_row25_traceSegment_057_0567_0009]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0540_0036 : g32p_coeffSegment g32p_row25_traceSegment_057 540 36 = [0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 540 18 18, g32p_row25_traceSegment_057_0540_0018, g32p_row25_traceSegment_057_0558_0018]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0504_0072 : g32p_coeffSegment g32p_row25_traceSegment_057 504 72 = [0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 504 36 36, g32p_row25_traceSegment_057_0504_0036, g32p_row25_traceSegment_057_0540_0036]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0432_0144 : g32p_coeffSegment g32p_row25_traceSegment_057 432 144 = [0, 8, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 432 72 72, g32p_row25_traceSegment_057_0432_0072, g32p_row25_traceSegment_057_0504_0072]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0288_0288 : g32p_coeffSegment g32p_row25_traceSegment_057 288 288 = [0, 12, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 288 144 144, g32p_row25_traceSegment_057_0288_0144, g32p_row25_traceSegment_057_0432_0144]
  decide +kernel

private theorem g32p_row25_traceSegment_057_0000_0576 : g32p_coeffSegment g32p_row25_traceSegment_057 0 576 = [0, 24, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row25_traceSegment_057 0 288 288, g32p_row25_traceSegment_057_0000_0288, g32p_row25_traceSegment_057_0288_0288]
  decide +kernel

theorem g32p_row25_traceCoefficients_057 :
    g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 57 = [0, 24, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row25_traceSegment_057_0000_0576

end HodgeLean.Foundations.Program

end
end
