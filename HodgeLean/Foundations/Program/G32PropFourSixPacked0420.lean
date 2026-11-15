import HodgeLean.Foundations.Program.G32PropFourSixPacked0419
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow38
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row37_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 10 = [0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 10) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 10) (g32p_literalTraceValue 36 10)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row37_traceCoefficients_010]
  decide +kernel

theorem g32p_row37_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 11 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 11) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 11) (g32p_literalTraceValue 36 11)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_011]
  decide +kernel

theorem g32p_row37_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 15 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 15) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 15) (g32p_literalTraceValue 36 15)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_015]
  decide +kernel

theorem g32p_row37_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 18 = [1, 0, 0, 1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 18) (g32p_literalTraceValue 36 18)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row37_traceCoefficients_018]
  decide +kernel

theorem g32p_row37_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 19 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 19) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 19) (g32p_literalTraceValue 36 19)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_019]
  decide +kernel

theorem g32p_row37_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 20 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 20) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 20) (g32p_literalTraceValue 36 20)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_020]
  decide +kernel

theorem g32p_row37_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 23 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 23) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 23) (g32p_literalTraceValue 36 23)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row37_traceCoefficients_023]
  decide +kernel

theorem g32p_row37_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 25 = [0, 0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 25) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 25) (g32p_literalTraceValue 36 25)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row37_traceCoefficients_025]
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

theorem g32p_row37_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 29 = [0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 29) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 29) (g32p_literalTraceValue 36 29)
      [1, -1, 1] [0, 432, 432] = true := by
  rw [g32p_row37_traceCoefficients_029]
  decide +kernel

theorem g32p_row37_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 32 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 32) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 32) (g32p_literalTraceValue 36 32)
      [1, -1, 1] [0, 0, 1296, 1296] = true := by
  rw [g32p_row37_traceCoefficients_032]
  decide +kernel

theorem g32p_row37_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 35 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 35) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 35) (g32p_literalTraceValue 36 35)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_035]
  decide +kernel

theorem g32p_row37_traceCoefficients_041 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 41 = [0, 0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_041 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 41) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 41) (g32p_literalTraceValue 36 41)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row37_traceCoefficients_041]
  decide +kernel

theorem g32p_row37_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 44 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 44) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 44) (g32p_literalTraceValue 36 44)
      [1, -1, 1] [0, 0, 3888, 3888] = true := by
  rw [g32p_row37_traceCoefficients_044]
  decide +kernel

theorem g32p_row37_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 45 = [0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 45) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 45) (g32p_literalTraceValue 36 45)
      [1, -1, 1] [1296, 1296, 1296] = true := by
  rw [g32p_row37_traceCoefficients_045]
  decide +kernel

theorem g32p_row37_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 56 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 56) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 56) (g32p_literalTraceValue 36 56)
      [1, -1, 1] [0, 0, 2592, 2592] = true := by
  rw [g32p_row37_traceCoefficients_056]
  decide +kernel

theorem g32p_row37_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 66 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 66) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 66) (g32p_literalTraceValue 36 66)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row37_traceCoefficients_066]
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

theorem g32p_row37_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 67 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 67) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 67) (g32p_literalTraceValue 36 67)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row37_traceCoefficients_067]
  decide +kernel

theorem g32p_row37_traceCoefficients_072 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 72 = [0, 6] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_072 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 72) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 72) (g32p_literalTraceValue 36 72)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row37_traceCoefficients_072]
  decide +kernel

theorem g32p_row37_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 76 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 76) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 76) (g32p_literalTraceValue 36 76)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_076]
  decide +kernel

theorem g32p_row37_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 77 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 77) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 77) (g32p_literalTraceValue 36 77)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row37_traceCoefficients_077]
  decide +kernel

theorem g32p_row37_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 79 = [0, 1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 79) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 79) (g32p_literalTraceValue 36 79)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row37_traceCoefficients_079]
  decide +kernel

theorem g32p_row37_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 81 = [0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 81) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 81) (g32p_literalTraceValue 36 81)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row37_traceCoefficients_081]
  decide +kernel

theorem g32p_row37_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 84 = [0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 84) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 84) (g32p_literalTraceValue 36 84)
      [1, -1, 1] [-1296] = true := by
  rw [g32p_row37_traceCoefficients_084]
  decide +kernel

theorem g32p_row37_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 86 = [0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 86) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 86) (g32p_literalTraceValue 36 86)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row37_traceCoefficients_086]
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

theorem g32p_row37_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 89 = [0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 89) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 89) (g32p_literalTraceValue 36 89)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row37_traceCoefficients_089]
  decide +kernel

theorem g32p_row37_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 92 = [0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 92) (g32p_literalTraceValue 36 92)
      [1, -1, 1] [-2592] = true := by
  rw [g32p_row37_traceCoefficients_092]
  decide +kernel

theorem g32p_row37_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 93 = [0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 93) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 93) (g32p_literalTraceValue 36 93)
      [1, -1, 1] [15552, 15552] = true := by
  rw [g32p_row37_traceCoefficients_093]
  decide +kernel

theorem g32p_row37_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 94 = [0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 94) (g32p_literalTraceValue 36 94)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row37_traceCoefficients_094]
  decide +kernel

theorem g32p_row37_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 95 = [0, 1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 95) (g32p_literalTraceValue 36 95)
      [1, -1, 1] [-3888] = true := by
  rw [g32p_row37_traceCoefficients_095]
  decide +kernel

theorem g32p_row37_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 98 = [0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 98) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 98) (g32p_literalTraceValue 36 98)
      [1, -1, 1] [15552, 15552] = true := by
  rw [g32p_row37_traceCoefficients_098]
  decide +kernel

theorem g32p_row37_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 99 = [0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 99) (g32p_literalTraceValue 36 99)
      [1, -1, 1] [155520, 155520] = true := by
  rw [g32p_row37_traceCoefficients_099]
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

def g32p_row37_generatorIndex : Fin 8 → Fin 408 :=
  ![36, 87, 138, 189, 276, 277, 378, 379]

theorem g32p_row37_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup27_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 36 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 36 g32p_row37_supplierClass
    g32p_row37_supplierClass_isConj g32p_supplierGroup27_support g32p_row37_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row37_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup27_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row37_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 36 c false (g32p_row37_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 36 c true (g32p_row37_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 36 c false (g32p_row37_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 36 c true (g32p_row37_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 36 c false (g32p_row37_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 36 c false (g32p_row37_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 36 c true (g32p_row37_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 36 c true (g32p_row37_coinduced_zero c hc true) 3

theorem g32p_row37_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup27_support →
      g32p_literalTraceValue (g32p_row37_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row37_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup27_support →
      g32p_literalTraceValue (g32p_row37_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row37_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup27_support →
      g32p_literalTraceValue (g32p_row37_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row37_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup27_support →
      g32p_literalTraceValue (g32p_row37_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row37_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup27_support →
      g32p_literalTraceValue (g32p_row37_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row37_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup27_support →
      g32p_literalTraceValue (g32p_row37_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row37_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup27_support →
      g32p_literalTraceValue (g32p_row37_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row37_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup27_support) :
    g32p_literalTraceValue (g32p_row37_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup27_support →
    g32p_literalTraceValue (g32p_row37_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row37_zeroTrace_block_00 r k
  · exact g32p_row37_zeroTrace_block_01 r k
  · exact g32p_row37_zeroTrace_block_02 r k
  · exact g32p_row37_zeroTrace_block_03 r k
  · exact g32p_row37_zeroTrace_block_04 r k
  · exact g32p_row37_zeroTrace_block_05 r k
  · exact g32p_row37_zeroTrace_block_06 r k

theorem g32p_row37_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup27_support) :
    (g32p_recordedInductionGenerators (g32p_row37_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row37_generatorIndex k) c) := by
  rw [g32p_row37_recordedGenerator_zero c hc k, g32p_row37_zeroTrace_arithmetic c k hc]
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

def g32p_row37_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [2592, 2592, 2592] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [432, 432, 432] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [432, 432, 432] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [1728, 1728] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [432, 432, 432] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [0, 0, 432, 432] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [0, 432, 432] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [0, 0, 1296, 1296] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [0, 0, 432, 432] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [0, 0, 3888, 3888] else (if i.val < 46 then [1296, 1296, 1296] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else [0, 0, 2592, 2592]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [0, 0, 432, 432] else (if i.val < 68 then [3888, 3888, 3888] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [-432] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [0, 0, 432, 432] else [])) else (if i.val < 80 then [-432] else (if i.val < 81 then [] else [1728, 1728]))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [-1296])) else (if i.val < 87 then (if i.val < 86 then [] else [-432]) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [1728, 1728] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [-2592] else (if i.val < 94 then [15552, 15552] else [1728, 1728]))) else (if i.val < 98 then (if i.val < 96 then [-3888] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [15552, 15552] else [155520, 155520]) else (if i.val < 101 then [] else [])))))))

theorem g32p_row37_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup27_support) :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) c) (g32p_literalTraceValue 36 c)
      [1, -1, 1] (g32p_row37_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row37_tracePolynomial_000
  · exact g32p_row37_tracePolynomial_001
  · exact g32p_row37_tracePolynomial_002
  · exact g32p_row37_tracePolynomial_003
  · exact g32p_row37_tracePolynomial_004
  · exact g32p_row37_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_007
  · exact g32p_row37_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_010
  · exact g32p_row37_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_018
  · exact g32p_row37_tracePolynomial_019
  · exact g32p_row37_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_023
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_044
  · exact g32p_row37_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_066
  · exact g32p_row37_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_076
  · exact g32p_row37_tracePolynomial_077
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_079
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_081
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_086
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_089
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_092
  · exact g32p_row37_tracePolynomial_093
  · exact g32p_row37_tracePolynomial_094
  · exact g32p_row37_tracePolynomial_095
  · exact False.elim ((by decide : (96 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact g32p_row37_tracePolynomial_098
  · exact g32p_row37_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup27_support) hc)
  · exact False.elim ((by decide : (101 : Fin 102) ∉ g32p_supplierGroup27_support) hc)

theorem g32p_row37_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 36 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 36 c) := by
  by_cases hc : c ∈ g32p_supplierGroup27_support
  · have hclass (j : Fin 144) :
        IsConj (g32p_literalRepresentative c) (g32p_row37_groupEquiv j : g32p_G) ↔
          g32p_row37_supplierClassifier j = c := by
      simpa only [g32p_row37_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row37_supplierClass_iff (g32p_row37_groupEquiv j) c
    have hχ (j : Fin 144) :
        (g32p_recordedSupplierCharacters 36 (g32p_row37_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row37_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 36 (show (g32p_recordedSuppliers 36).H from g32p_row37_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row37_characterValues (g32p_row37_groupEquiv.symm (g32p_row37_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 36).H (g32p_recordedSupplierCharacters 36)
      (g32p_literalRepresentative c) g32p_row37_groupEquiv g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) c 6 144
      (g32p_literalCentralizer c) (g32p_literalTraceValue 36 c) [1, -1, 1]
      (g32p_row37_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row37_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 36)))
      (g32p_row37_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row37_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row37_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
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

theorem g32p_row37_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
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

theorem g32p_row37_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
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

theorem g32p_row37_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
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

theorem g32p_row37_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
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

theorem g32p_row37_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
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

theorem g32p_row37_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row37_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row37_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
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

theorem g32p_row37_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row37_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row37_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row37_variantArithmetic_00_0 r
  · exact g32p_row37_variantArithmetic_01_0 r
  · exact g32p_row37_variantArithmetic_02_0 r
  · exact g32p_row37_variantArithmetic_03_0 r
  · exact g32p_row37_variantArithmetic_04_0 r
  · exact g32p_row37_variantArithmetic_05_0 r
  · exact g32p_row37_variantArithmetic_06_0 r

theorem g32p_row37_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row37_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row37_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row37_variantArithmetic_00_1 r
  · exact g32p_row37_variantArithmetic_01_1 r
  · exact g32p_row37_variantArithmetic_02_1 r
  · exact g32p_row37_variantArithmetic_03_1 r
  · exact g32p_row37_variantArithmetic_04_1 r
  · exact g32p_row37_variantArithmetic_05_1 r
  · exact g32p_row37_variantArithmetic_06_1 r

theorem g32p_row37_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row37_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row37_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row37_variantArithmetic_00_2 r
  · exact g32p_row37_variantArithmetic_01_2 r
  · exact g32p_row37_variantArithmetic_02_2 r
  · exact g32p_row37_variantArithmetic_03_2 r
  · exact g32p_row37_variantArithmetic_04_2 r
  · exact g32p_row37_variantArithmetic_05_2 r
  · exact g32p_row37_variantArithmetic_06_2 r

theorem g32p_row37_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row37_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row37_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row37_variantArithmetic_00_3 r
  · exact g32p_row37_variantArithmetic_01_3 r
  · exact g32p_row37_variantArithmetic_02_3 r
  · exact g32p_row37_variantArithmetic_03_3 r
  · exact g32p_row37_variantArithmetic_04_3 r
  · exact g32p_row37_variantArithmetic_05_3 r
  · exact g32p_row37_variantArithmetic_06_3 r

theorem g32p_row37_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row37_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row37_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row37_variantArithmetic_00_4 r
  · exact g32p_row37_variantArithmetic_01_4 r
  · exact g32p_row37_variantArithmetic_02_4 r
  · exact g32p_row37_variantArithmetic_03_4 r
  · exact g32p_row37_variantArithmetic_04_4 r
  · exact g32p_row37_variantArithmetic_05_4 r
  · exact g32p_row37_variantArithmetic_06_4 r

theorem g32p_row37_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row37_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row37_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row37_variantArithmetic_00_5 r
  · exact g32p_row37_variantArithmetic_01_5 r
  · exact g32p_row37_variantArithmetic_02_5 r
  · exact g32p_row37_variantArithmetic_03_5 r
  · exact g32p_row37_variantArithmetic_04_5 r
  · exact g32p_row37_variantArithmetic_05_5 r
  · exact g32p_row37_variantArithmetic_06_5 r

theorem g32p_row37_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row37_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row37_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row37_variantArithmetic_00_6 r
  · exact g32p_row37_variantArithmetic_01_6 r
  · exact g32p_row37_variantArithmetic_02_6 r
  · exact g32p_row37_variantArithmetic_03_6 r
  · exact g32p_row37_variantArithmetic_04_6 r
  · exact g32p_row37_variantArithmetic_05_6 r
  · exact g32p_row37_variantArithmetic_06_6 r

theorem g32p_row37_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row37_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row37_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 36 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row37_variantArithmetic_00_7 r
  · exact g32p_row37_variantArithmetic_01_7 r
  · exact g32p_row37_variantArithmetic_02_7 r
  · exact g32p_row37_variantArithmetic_03_7 r
  · exact g32p_row37_variantArithmetic_04_7 r
  · exact g32p_row37_variantArithmetic_05_7 r
  · exact g32p_row37_variantArithmetic_06_7 r

theorem g32p_row37_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row37_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row37_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 36 c _ (g32p_row37_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row37_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 36 c _ (g32p_row37_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row37_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 36 c _ (g32p_row37_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row37_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 36 c _ (g32p_row37_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row37_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 36 c _ (g32p_row37_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row37_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 36 c _ (g32p_row37_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row37_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 36 c _ (g32p_row37_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row37_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 36 c _ (g32p_row37_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row37_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup28_source : Fin 144 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (25, 200)) else (if i.val < 3 then (57, 102) else (30, 187))) else (if i.val < 6 then (if i.val < 5 then (80, 26) else (10, 83)) else (if i.val < 7 then (20, 121) else (if i.val < 8 then (11, 180) else (123, 72))))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then (30, 40) else (87, 157)) else (if i.val < 12 then (47, 109) else (10, 188))) else (if i.val < 15 then (if i.val < 14 then (14, 92) else (90, 20)) else (if i.val < 16 then (80, 162) else (if i.val < 17 then (113, 72) else (108, 233)))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then (0, 88) else (6, 197)) else (if i.val < 21 then (49, 68) else (12, 188))) else (if i.val < 24 then (if i.val < 23 then (56, 151) else (51, 101)) else (if i.val < 25 then (0, 99) else (if i.val < 26 then (50, 70) else (12, 228))))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then (73, 61) else (88, 207)) else (if i.val < 30 then (27, 194) else (17, 229))) else (if i.val < 33 then (if i.val < 32 then (7, 199) else (129, 178)) else (if i.val < 34 then (56, 88) else (if i.val < 35 then (101, 224) else (92, 159))))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then (7, 244) else (66, 165)) else (if i.val < 39 then (128, 104) else (63, 38))) else (if i.val < 42 then (if i.val < 41 then (86, 197) else (36, 183)) else (if i.val < 43 then (72, 172) else (if i.val < 44 then (16, 50) else (109, 158))))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then (89, 187) else (87, 158)) else (if i.val < 48 then (49, 210) else (33, 13))) else (if i.val < 51 then (if i.val < 50 then (37, 15) else (4, 243)) else (if i.val < 52 then (5, 194) else (if i.val < 53 then (80, 80) else (24, 132)))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then (17, 213) else (27, 15)) else (if i.val < 57 then (33, 14) else (106, 24))) else (if i.val < 60 then (if i.val < 59 then (17, 219) else (93, 230)) else (if i.val < 61 then (77, 75) else (if i.val < 62 then (14, 223) else (132, 52))))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then (17, 232) else (31, 203)) else (if i.val < 66 then (35, 3) else (8, 48))) else (if i.val < 69 then (if i.val < 68 then (54, 139) else (57, 187)) else (if i.val < 70 then (18, 246) else (if i.val < 71 then (138, 208) else (24, 69)))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then (87, 218) else (44, 239)) else (if i.val < 75 then (113, 231) else (109, 218))) else (if i.val < 78 then (if i.val < 77 then (113, 164) else (60, 230)) else (if i.val < 79 then (47, 193) else (if i.val < 80 then (53, 94) else (126, 149))))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then (132, 76) else (107, 123)) else (if i.val < 84 then (62, 239) else (31, 170))) else (if i.val < 87 then (if i.val < 86 then (85, 179) else (142, 0)) else (if i.val < 88 then (56, 57) else (if i.val < 89 then (102, 48) else (120, 4)))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then (85, 244) else (85, 143)) else (if i.val < 93 then (62, 224) else (125, 81))) else (if i.val < 96 then (if i.val < 95 then (62, 201) else (106, 181)) else (if i.val < 97 then (6, 75) else (if i.val < 98 then (109, 62) else (31, 111))))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then (83, 158) else (5, 18)) else (if i.val < 102 then (100, 135) else (125, 77))) else (if i.val < 105 then (if i.val < 104 then (0, 167) else (6, 27)) else (if i.val < 106 then (48, 68) else (if i.val < 107 then (136, 67) else (28, 195))))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then (15, 23) else (122, 85)) else (if i.val < 111 then (66, 104) else (3, 21))) else (if i.val < 114 then (if i.val < 113 then (138, 175) else (100, 226)) else (if i.val < 115 then (26, 6) else (if i.val < 116 then (118, 245) else (71, 3))))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then (119, 233) else (100, 218)) else (if i.val < 120 then (135, 162) else (135, 94))) else (if i.val < 123 then (if i.val < 122 then (143, 73) else (118, 113)) else (if i.val < 124 then (54, 174) else (if i.val < 125 then (102, 58) else (115, 86)))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then (105, 162) else (105, 107)) else (if i.val < 129 then (37, 46) else (131, 74))) else (if i.val < 132 then (if i.val < 131 then (125, 160) else (32, 142)) else (if i.val < 133 then (111, 75) else (if i.val < 134 then (139, 173) else (60, 180))))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then (55, 48) else (57, 159)) else (if i.val < 138 then (96, 11) else (6, 234))) else (if i.val < 141 then (if i.val < 140 then (120, 3) else (130, 70)) else (if i.val < 142 then (143, 62) else (if i.val < 143 then (120, 165) else (92, 88)))))))))

def g32p_supplierGroup28_classify : Fin 144 → Fin 102 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 56) else (if i.val < 3 then 5 else 94)) else (if i.val < 6 then (if i.val < 5 then 87 else 18) else (if i.val < 7 then 4 else (if i.val < 8 then 56 else 50)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 95 else 50) else (if i.val < 12 then 56 else 18)) else (if i.val < 15 then (if i.val < 14 then 94 else 64) else (if i.val < 16 then 94 else (if i.val < 17 then 50 else 94))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then 88 else 5) else (if i.val < 21 then 64 else 88)) else (if i.val < 24 then (if i.val < 23 then 100 else 91) else (if i.val < 25 then 99 else (if i.val < 26 then 59 else 92)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then 45 else 59) else (if i.val < 30 then 59 else 50)) else (if i.val < 33 then (if i.val < 32 then 11 else 72) else (if i.val < 34 then 92 else (if i.val < 35 then 50 else 7)))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then 56 else 72) else (if i.val < 39 then 7 else 32)) else (if i.val < 42 then (if i.val < 41 then 23 else 59) else (if i.val < 43 then 50 else (if i.val < 44 then 5 else 94)))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then 64 else 11) else (if i.val < 48 then 91 else 5)) else (if i.val < 51 then (if i.val < 50 then 64 else 88) else (if i.val < 52 then 100 else (if i.val < 53 then 92 else 11))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then 50 else 88) else (if i.val < 57 then 5 else 91)) else (if i.val < 60 then (if i.val < 59 then 51 else 72) else (if i.val < 61 then 91 else (if i.val < 62 then 100 else 7)))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then 51 else 100) else (if i.val < 66 then 51 else 51)) else (if i.val < 69 then (if i.val < 68 then 94 else 5) else (if i.val < 70 then 59 else (if i.val < 71 then 59 else 45))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 10 else 45) else (if i.val < 75 then 10 else 76)) else (if i.val < 78 then (if i.val < 77 then 10 else 4) else (if i.val < 79 then 50 else (if i.val < 80 then 79 else 59)))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then 7 else 67) else (if i.val < 84 then 15 else 92)) else (if i.val < 87 then (if i.val < 86 then 4 else 7) else (if i.val < 88 then 35 else (if i.val < 89 then 45 else 7))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then 15 else 10) else (if i.val < 93 then 35 else 15)) else (if i.val < 96 then (if i.val < 95 then 35 else 66) else (if i.val < 97 then 4 else (if i.val < 98 then 72 else 87)))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then 11 else 87) else (if i.val < 102 then 85 else 59)) else (if i.val < 105 then (if i.val < 104 then 28 else 28) else (if i.val < 106 then 85 else (if i.val < 107 then 72 else 87)))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 28 else 85) else (if i.val < 111 then 72 else 28)) else (if i.val < 114 then (if i.val < 113 then 86 else 84) else (if i.val < 115 then 84 else (if i.val < 116 then 20 else 84)))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 41 else 84) else (if i.val < 120 then 20 else 41)) else (if i.val < 123 then (if i.val < 122 then 20 else 41) else (if i.val < 124 then 77 else (if i.val < 125 then 86 else 15))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then 66 else 35) else (if i.val < 129 then 32 else 86)) else (if i.val < 132 then (if i.val < 131 then 66 else 32) else (if i.val < 133 then 86 else (if i.val < 134 then 66 else 32)))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then 85 else 19) else (if i.val < 138 then 41 else 44)) else (if i.val < 141 then (if i.val < 140 then 20 else 41) else (if i.val < 142 then 20 else (if i.val < 143 then 41 else 20))))))))

def g32p_supplierGroup28_support : Finset (Fin 102) :=
  {0, 4, 5, 7, 10, 11, 15, 18, 19, 20, 23, 28, 32, 35, 41, 44, 45, 50, 51, 56, 59, 64, 66, 67, 72, 76, 77, 79, 84, 85, 86, 87, 88, 91, 92, 94, 95, 99, 100}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup28_matrix_000 : ∀ r : Fin 16,
    g32p_row38_groupNodes (g32p_finBlockIndex 144 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 0 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup28_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 0 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 0 r)).2 =
      g32p_supplierGroup28_classify (g32p_finBlockIndex 144 0 r) := by
  decide +kernel

theorem g32p_supplierGroup28_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup28_classify (g32p_finBlockIndex 144 0 r) ∈ g32p_supplierGroup28_support := by
  decide +kernel

theorem g32p_supplierGroup28_matrix_001 : ∀ r : Fin 16,
    g32p_row38_groupNodes (g32p_finBlockIndex 144 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 1 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup28_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 1 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 1 r)).2 =
      g32p_supplierGroup28_classify (g32p_finBlockIndex 144 1 r) := by
  decide +kernel

theorem g32p_supplierGroup28_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup28_classify (g32p_finBlockIndex 144 1 r) ∈ g32p_supplierGroup28_support := by
  decide +kernel

theorem g32p_supplierGroup28_matrix_002 : ∀ r : Fin 16,
    g32p_row38_groupNodes (g32p_finBlockIndex 144 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 2 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup28_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 2 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 2 r)).2 =
      g32p_supplierGroup28_classify (g32p_finBlockIndex 144 2 r) := by
  decide +kernel

theorem g32p_supplierGroup28_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup28_classify (g32p_finBlockIndex 144 2 r) ∈ g32p_supplierGroup28_support := by
  decide +kernel

theorem g32p_supplierGroup28_matrix_003 : ∀ r : Fin 16,
    g32p_row38_groupNodes (g32p_finBlockIndex 144 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 3 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup28_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 3 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 3 r)).2 =
      g32p_supplierGroup28_classify (g32p_finBlockIndex 144 3 r) := by
  decide +kernel

theorem g32p_supplierGroup28_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup28_classify (g32p_finBlockIndex 144 3 r) ∈ g32p_supplierGroup28_support := by
  decide +kernel

theorem g32p_supplierGroup28_matrix_004 : ∀ r : Fin 16,
    g32p_row38_groupNodes (g32p_finBlockIndex 144 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 4 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup28_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 4 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 4 r)).2 =
      g32p_supplierGroup28_classify (g32p_finBlockIndex 144 4 r) := by
  decide +kernel

theorem g32p_supplierGroup28_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup28_classify (g32p_finBlockIndex 144 4 r) ∈ g32p_supplierGroup28_support := by
  decide +kernel

theorem g32p_supplierGroup28_matrix_005 : ∀ r : Fin 16,
    g32p_row38_groupNodes (g32p_finBlockIndex 144 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 5 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup28_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 5 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 5 r)).2 =
      g32p_supplierGroup28_classify (g32p_finBlockIndex 144 5 r) := by
  decide +kernel

theorem g32p_supplierGroup28_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup28_classify (g32p_finBlockIndex 144 5 r) ∈ g32p_supplierGroup28_support := by
  decide +kernel

theorem g32p_supplierGroup28_matrix_006 : ∀ r : Fin 16,
    g32p_row38_groupNodes (g32p_finBlockIndex 144 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 6 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup28_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 6 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 6 r)).2 =
      g32p_supplierGroup28_classify (g32p_finBlockIndex 144 6 r) := by
  decide +kernel

theorem g32p_supplierGroup28_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup28_classify (g32p_finBlockIndex 144 6 r) ∈ g32p_supplierGroup28_support := by
  decide +kernel

theorem g32p_supplierGroup28_matrix_007 : ∀ r : Fin 16,
    g32p_row38_groupNodes (g32p_finBlockIndex 144 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 7 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup28_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 7 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 7 r)).2 =
      g32p_supplierGroup28_classify (g32p_finBlockIndex 144 7 r) := by
  decide +kernel

theorem g32p_supplierGroup28_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup28_classify (g32p_finBlockIndex 144 7 r) ∈ g32p_supplierGroup28_support := by
  decide +kernel

theorem g32p_supplierGroup28_matrix_008 : ∀ r : Fin 16,
    g32p_row38_groupNodes (g32p_finBlockIndex 144 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 8 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup28_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup28_source (g32p_finBlockIndex 144 8 r)).1 (g32p_supplierGroup28_source (g32p_finBlockIndex 144 8 r)).2 =
      g32p_supplierGroup28_classify (g32p_finBlockIndex 144 8 r) := by
  decide +kernel

theorem g32p_supplierGroup28_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup28_classify (g32p_finBlockIndex 144 8 r) ∈ g32p_supplierGroup28_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
