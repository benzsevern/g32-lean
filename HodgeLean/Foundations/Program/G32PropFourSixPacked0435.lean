import HodgeLean.Foundations.Program.G32PropFourSixPacked0434
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row47_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 35 = [4, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 35) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 35) (g32p_literalTraceValue 46 35)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_035]
  decide +kernel

theorem g32p_row47_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 37 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 37) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 37) (g32p_literalTraceValue 46 37)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row47_traceCoefficients_037]
  decide +kernel

theorem g32p_row47_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 40 = [0, 4, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 40) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 40) (g32p_literalTraceValue 46 40)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_040]
  decide +kernel

theorem g32p_row47_traceCoefficients_041 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 41 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_041 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 41) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 41) (g32p_literalTraceValue 46 41)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_041]
  decide +kernel

theorem g32p_row47_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 43 = [8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 43) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 43) (g32p_literalTraceValue 46 43)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_043]
  decide +kernel

theorem g32p_row47_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 44 = [0, 4, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 44) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 44) (g32p_literalTraceValue 46 44)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row47_traceCoefficients_044]
  decide +kernel

theorem g32p_row47_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 45 = [4, 0, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 45) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 45) (g32p_literalTraceValue 46 45)
      [1, 1, 1] [1296] = true := by
  rw [g32p_row47_traceCoefficients_045]
  decide +kernel

theorem g32p_row47_traceCoefficients_048 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 48 = [6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_048 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 48) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 48) (g32p_literalTraceValue 46 48)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_048]
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

theorem g32p_row47_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 50 = [0, 8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 50) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 50) (g32p_literalTraceValue 46 50)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_050]
  decide +kernel

theorem g32p_row47_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 51 = [4, 0, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 51) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 51) (g32p_literalTraceValue 46 51)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_051]
  decide +kernel

theorem g32p_row47_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 52 = [0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 52) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 52) (g32p_literalTraceValue 46 52)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_052]
  decide +kernel

theorem g32p_row47_traceCoefficients_055 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 55 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_055 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 55) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 55) (g32p_literalTraceValue 46 55)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_055]
  decide +kernel

theorem g32p_row47_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 56 = [0, 8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 56) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 56) (g32p_literalTraceValue 46 56)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_056]
  decide +kernel

theorem g32p_row47_traceCoefficients_058 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 58 = [6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_058 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 58) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 58) (g32p_literalTraceValue 46 58)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_058]
  decide +kernel

theorem g32p_row47_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 59 = [0, 0, 8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 59) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 59) (g32p_literalTraceValue 46 59)
      [1, 1, 1] [864] = true := by
  rw [g32p_row47_traceCoefficients_059]
  decide +kernel

theorem g32p_row47_traceCoefficients_061 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 61 = [0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_061 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 61) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 61) (g32p_literalTraceValue 46 61)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_061]
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

theorem g32p_row47_traceCoefficients_063 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 63 = [6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_063 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 63) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 63) (g32p_literalTraceValue 46 63)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_063]
  decide +kernel

theorem g32p_row47_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 64 = [4, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 64) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 64) (g32p_literalTraceValue 46 64)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_064]
  decide +kernel

theorem g32p_row47_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 65 = [0, 0, 2] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 65) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 65) (g32p_literalTraceValue 46 65)
      [1, 1, 1] [3456] = true := by
  rw [g32p_row47_traceCoefficients_065]
  decide +kernel

theorem g32p_row47_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 66 = [4, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 66) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 66) (g32p_literalTraceValue 46 66)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_066]
  decide +kernel

theorem g32p_row47_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 67 = [0, 1, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 67) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 67) (g32p_literalTraceValue 46 67)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row47_traceCoefficients_067]
  decide +kernel

theorem g32p_row47_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 71 = [0, 4, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 71) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 71) (g32p_literalTraceValue 46 71)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_071]
  decide +kernel

theorem g32p_row47_traceCoefficients_072 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 72 = [0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_072 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 72) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 72) (g32p_literalTraceValue 46 72)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_072]
  decide +kernel

theorem g32p_row47_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 74 = [8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 74) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 74) (g32p_literalTraceValue 46 74)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_074]
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

theorem g32p_row47_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 75 = [0, 4, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 75) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 75) (g32p_literalTraceValue 46 75)
      [1, 1, 1] [1296] = true := by
  rw [g32p_row47_traceCoefficients_075]
  decide +kernel

theorem g32p_row47_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 76 = [0, 4, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 76) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 76) (g32p_literalTraceValue 46 76)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row47_traceCoefficients_076]
  decide +kernel

theorem g32p_row47_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 77 = [0, 4, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 77) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 77) (g32p_literalTraceValue 46 77)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_077]
  decide +kernel

theorem g32p_row47_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 78 = [8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 78) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 78) (g32p_literalTraceValue 46 78)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_078]
  decide +kernel

theorem g32p_row47_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 79 = [0, 1, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 79) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 79) (g32p_literalTraceValue 46 79)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row47_traceCoefficients_079]
  decide +kernel

theorem g32p_row47_traceCoefficients_080 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 80 = [6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_080 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 80) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 80) (g32p_literalTraceValue 46 80)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_080]
  decide +kernel

theorem g32p_row47_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 81 = [1, 0, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 81) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 81) (g32p_literalTraceValue 46 81)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row47_traceCoefficients_081]
  decide +kernel

theorem g32p_row47_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 82 = [0, 2] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 82) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 82) (g32p_literalTraceValue 46 82)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_082]
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

theorem g32p_row47_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 83 = [0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 83) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 83) (g32p_literalTraceValue 46 83)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_083]
  decide +kernel

theorem g32p_row47_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 84 = [4, 0, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 84) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 84) (g32p_literalTraceValue 46 84)
      [1, 1, 1] [1296] = true := by
  rw [g32p_row47_traceCoefficients_084]
  decide +kernel

theorem g32p_row47_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 85 = [4, 0, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 85) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 85) (g32p_literalTraceValue 46 85)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_085]
  decide +kernel

theorem g32p_row47_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 86 = [4, 0, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 86) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 86) (g32p_literalTraceValue 46 86)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_086]
  decide +kernel

theorem g32p_row47_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 87 = [4, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 87) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 87) (g32p_literalTraceValue 46 87)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_087]
  decide +kernel

theorem g32p_row47_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 88 = [4, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 88) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 88) (g32p_literalTraceValue 46 88)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_088]
  decide +kernel

theorem g32p_row47_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 89 = [1, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 89) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 89) (g32p_literalTraceValue 46 89)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_089]
  decide +kernel

theorem g32p_row47_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 90 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 90) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 90) (g32p_literalTraceValue 46 90)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row47_traceCoefficients_090]
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

theorem g32p_row47_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 91 = [4, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 91) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 91) (g32p_literalTraceValue 46 91)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_091]
  decide +kernel

theorem g32p_row47_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 92 = [0, 0, 8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 92) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 92) (g32p_literalTraceValue 46 92)
      [1, 1, 1] [5184] = true := by
  rw [g32p_row47_traceCoefficients_092]
  decide +kernel

theorem g32p_row47_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 93 = [1, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 93) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 93) (g32p_literalTraceValue 46 93)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_093]
  decide +kernel

theorem g32p_row47_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 94 = [6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 94) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 94) (g32p_literalTraceValue 46 94)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_094]
  decide +kernel

theorem g32p_row47_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 95 = [0, 1, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 95) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 95) (g32p_literalTraceValue 46 95)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row47_traceCoefficients_095]
  decide +kernel

theorem g32p_row47_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 96 = [0, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 96) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 96) (g32p_literalTraceValue 46 96)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_096]
  decide +kernel

theorem g32p_row47_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 97 = [0, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 97) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 97) (g32p_literalTraceValue 46 97)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_097]
  decide +kernel

theorem g32p_row47_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 98 = [1, 0, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 98) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 98) (g32p_literalTraceValue 46 98)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row47_traceCoefficients_098]
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

theorem g32p_row47_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 99 = [1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 99) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 99) (g32p_literalTraceValue 46 99)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_099]
  decide +kernel

theorem g32p_row47_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 100 = [4, 0, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 100) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 100) (g32p_literalTraceValue 46 100)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row47_traceCoefficients_100]
  decide +kernel

theorem g32p_row47_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 101 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 101) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 101) (g32p_literalTraceValue 46 101)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row47_traceCoefficients_101]
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

def g32p_row47_generatorIndex : Fin 8 → Fin 408 :=
  ![46, 97, 148, 199, 296, 297, 398, 399]

theorem g32p_row47_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup24_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 46 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 46 g32p_row47_supplierClass
    g32p_row47_supplierClass_isConj g32p_supplierGroup24_support g32p_row47_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row47_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup24_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row47_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 46 c false (g32p_row47_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 46 c true (g32p_row47_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 46 c false (g32p_row47_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 46 c true (g32p_row47_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 46 c false (g32p_row47_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 46 c false (g32p_row47_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 46 c true (g32p_row47_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 46 c true (g32p_row47_coinduced_zero c hc true) 3

theorem g32p_row47_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row47_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row47_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row47_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row47_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row47_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row47_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row47_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row47_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row47_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row47_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row47_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row47_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row47_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row47_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup24_support) :
    g32p_literalTraceValue (g32p_row47_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup24_support →
    g32p_literalTraceValue (g32p_row47_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row47_zeroTrace_block_00 r k
  · exact g32p_row47_zeroTrace_block_01 r k
  · exact g32p_row47_zeroTrace_block_02 r k
  · exact g32p_row47_zeroTrace_block_03 r k
  · exact g32p_row47_zeroTrace_block_04 r k
  · exact g32p_row47_zeroTrace_block_05 r k
  · exact g32p_row47_zeroTrace_block_06 r k

theorem g32p_row47_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup24_support) :
    (g32p_recordedInductionGenerators (g32p_row47_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row47_generatorIndex k) c) := by
  rw [g32p_row47_recordedGenerator_zero c hc k, g32p_row47_zeroTrace_arithmetic c k hc]
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

def g32p_row47_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [15552] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [5184] else []))) else (if i.val < 9 then (if i.val < 7 then [1296] else (if i.val < 8 then [] else [1728])) else (if i.val < 10 then [] else (if i.val < 11 then [432] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [432] else [432])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [1728] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [432])) else (if i.val < 29 then [3888] else (if i.val < 30 then [864] else []))) else (if i.val < 34 then (if i.val < 32 then [1728] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [432])) else (if i.val < 42 then [432] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [3888] else (if i.val < 46 then [1296] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [432] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [432] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [864])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [3456])) else (if i.val < 67 then [] else (if i.val < 68 then [15552] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [432])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else [1296]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [3888] else (if i.val < 78 then [432] else [])) else (if i.val < 80 then [1728] else (if i.val < 81 then [] else [1728]))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [1296])) else (if i.val < 87 then (if i.val < 86 then [432] else [432]) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [1728] else [])) else (if i.val < 93 then [5184] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [15552] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [15552] else []) else (if i.val < 101 then [3888] else [155520])))))))

theorem g32p_row47_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup24_support) :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) c) (g32p_literalTraceValue 46 c)
      [1, 1, 1] (g32p_row47_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row47_tracePolynomial_000
  · exact g32p_row47_tracePolynomial_001
  · exact g32p_row47_tracePolynomial_002
  · exact g32p_row47_tracePolynomial_003
  · exact g32p_row47_tracePolynomial_004
  · exact g32p_row47_tracePolynomial_005
  · exact g32p_row47_tracePolynomial_006
  · exact g32p_row47_tracePolynomial_007
  · exact g32p_row47_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_010
  · exact g32p_row47_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_017
  · exact g32p_row47_tracePolynomial_018
  · exact g32p_row47_tracePolynomial_019
  · exact g32p_row47_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_023
  · exact g32p_row47_tracePolynomial_024
  · exact g32p_row47_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_027
  · exact g32p_row47_tracePolynomial_028
  · exact g32p_row47_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_031
  · exact g32p_row47_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_040
  · exact g32p_row47_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_043
  · exact g32p_row47_tracePolynomial_044
  · exact g32p_row47_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_048
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_050
  · exact g32p_row47_tracePolynomial_051
  · exact g32p_row47_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_055
  · exact g32p_row47_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_058
  · exact g32p_row47_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_061
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_063
  · exact g32p_row47_tracePolynomial_064
  · exact g32p_row47_tracePolynomial_065
  · exact g32p_row47_tracePolynomial_066
  · exact g32p_row47_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_071
  · exact g32p_row47_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row47_tracePolynomial_074
  · exact g32p_row47_tracePolynomial_075
  · exact g32p_row47_tracePolynomial_076
  · exact g32p_row47_tracePolynomial_077
  · exact g32p_row47_tracePolynomial_078
  · exact g32p_row47_tracePolynomial_079
  · exact g32p_row47_tracePolynomial_080
  · exact g32p_row47_tracePolynomial_081
  · exact g32p_row47_tracePolynomial_082
  · exact g32p_row47_tracePolynomial_083
  · exact g32p_row47_tracePolynomial_084
  · exact g32p_row47_tracePolynomial_085
  · exact g32p_row47_tracePolynomial_086
  · exact g32p_row47_tracePolynomial_087
  · exact g32p_row47_tracePolynomial_088
  · exact g32p_row47_tracePolynomial_089
  · exact g32p_row47_tracePolynomial_090
  · exact g32p_row47_tracePolynomial_091
  · exact g32p_row47_tracePolynomial_092
  · exact g32p_row47_tracePolynomial_093
  · exact g32p_row47_tracePolynomial_094
  · exact g32p_row47_tracePolynomial_095
  · exact g32p_row47_tracePolynomial_096
  · exact g32p_row47_tracePolynomial_097
  · exact g32p_row47_tracePolynomial_098
  · exact g32p_row47_tracePolynomial_099
  · exact g32p_row47_tracePolynomial_100
  · exact g32p_row47_tracePolynomial_101

theorem g32p_row47_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 46 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 46 c) := by
  by_cases hc : c ∈ g32p_supplierGroup24_support
  · have hclass (j : Fin 432) :
        IsConj (g32p_literalRepresentative c) (g32p_row33_groupEquiv j : g32p_G) ↔
          g32p_row47_supplierClassifier j = c := by
      simpa only [g32p_row47_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row47_supplierClass_iff (g32p_row33_groupEquiv j) c
    have hχ (j : Fin 432) :
        (g32p_recordedSupplierCharacters 46 (g32p_row33_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row47_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 46 (show (g32p_recordedSuppliers 46).H from g32p_row33_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row47_characterValues (g32p_row33_groupEquiv.symm (g32p_row33_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 46).H (g32p_recordedSupplierCharacters 46)
      (g32p_literalRepresentative c) g32p_row33_groupEquiv g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) c 3 432
      (g32p_literalCentralizer c) (g32p_literalTraceValue 46 c) [1, 1, 1]
      (g32p_row47_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row47_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 46)))
      (g32p_row47_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row47_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row47_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
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

theorem g32p_row47_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
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

theorem g32p_row47_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
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

theorem g32p_row47_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
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

theorem g32p_row47_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
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

theorem g32p_row47_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
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

theorem g32p_row47_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row47_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row47_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 46 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
