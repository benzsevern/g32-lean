import HodgeLean.Foundations.Program.G32PropFourSixPacked0429
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

theorem g32p_row43_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 23 = [0, 0, 1, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 23) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 23) (g32p_literalTraceValue 42 23)
      [1, -1, 1] [0, 0, 1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_023]
  decide +kernel

theorem g32p_row43_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 24 = [0, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 24) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 24) (g32p_literalTraceValue 42 24)
      [1, -1, 1] [-2592, 0, 2592, 2592] = true := by
  rw [g32p_row43_traceCoefficients_024]
  decide +kernel

theorem g32p_row43_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 25 = [0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 25) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 25) (g32p_literalTraceValue 42 25)
      [1, -1, 1] [0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_025]
  decide +kernel

theorem g32p_row43_traceCoefficients_027 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 27 = [0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_027 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 27) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 27) (g32p_literalTraceValue 42 27)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row43_traceCoefficients_027]
  decide +kernel

theorem g32p_row43_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 28 = [0, 5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 28) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 28) (g32p_literalTraceValue 42 28)
      [1, -1, 1] [-19440] = true := by
  rw [g32p_row43_traceCoefficients_028]
  decide +kernel

theorem g32p_row43_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 29 = [0, 0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 29) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 29) (g32p_literalTraceValue 42 29)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_029]
  decide +kernel

theorem g32p_row43_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 31 = [0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 31) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 31) (g32p_literalTraceValue 42 31)
      [1, -1, 1] [-1728] = true := by
  rw [g32p_row43_traceCoefficients_031]
  decide +kernel

theorem g32p_row43_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 32 = [0, 8] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 32) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 32) (g32p_literalTraceValue 42 32)
      [1, -1, 1] [-2592] = true := by
  rw [g32p_row43_traceCoefficients_032]
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

theorem g32p_row43_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 35 = [0, 0, 0, 0, 8] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 35) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 35) (g32p_literalTraceValue 42 35)
      [1, -1, 1] [2592, 2592, 2592] = true := by
  rw [g32p_row43_traceCoefficients_035]
  decide +kernel

theorem g32p_row43_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 37 = [0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 37) (g32p_literalTraceValue 42 37)
      [1, -1, 1] [-155520] = true := by
  rw [g32p_row43_traceCoefficients_037]
  decide +kernel

theorem g32p_row43_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 40 = [4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 40) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 40) (g32p_literalTraceValue 42 40)
      [1, -1, 1] [432, 432] = true := by
  rw [g32p_row43_traceCoefficients_040]
  decide +kernel

theorem g32p_row43_traceCoefficients_041 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 41 = [0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_041 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 41) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 41) (g32p_literalTraceValue 42 41)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row43_traceCoefficients_041]
  decide +kernel

theorem g32p_row43_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 43 = [0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 43) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 43) (g32p_literalTraceValue 42 43)
      [1, -1, 1] [0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_043]
  decide +kernel

theorem g32p_row43_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 44 = [0, 5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 44) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 44) (g32p_literalTraceValue 42 44)
      [1, -1, 1] [-19440] = true := by
  rw [g32p_row43_traceCoefficients_044]
  decide +kernel

theorem g32p_row43_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 45 = [0, 0, 8] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 45) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 45) (g32p_literalTraceValue 42 45)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_045]
  decide +kernel

theorem g32p_row43_traceCoefficients_048 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 48 = [6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_048 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 48) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 48) (g32p_literalTraceValue 42 48)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_048]
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

theorem g32p_row43_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 50 = [4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 50) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 50) (g32p_literalTraceValue 42 50)
      [1, -1, 1] [432, 432] = true := by
  rw [g32p_row43_traceCoefficients_050]
  decide +kernel

theorem g32p_row43_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 51 = [0, 4, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 51) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 51) (g32p_literalTraceValue 42 51)
      [1, -1, 1] [-1296, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_051]
  decide +kernel

theorem g32p_row43_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 52 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 52) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 52) (g32p_literalTraceValue 42 52)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_052]
  decide +kernel

theorem g32p_row43_traceCoefficients_055 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 55 = [0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_055 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 55) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 55) (g32p_literalTraceValue 42 55)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_055]
  decide +kernel

theorem g32p_row43_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 56 = [0, 4, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 56) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 56) (g32p_literalTraceValue 42 56)
      [1, -1, 1] [0, 2592] = true := by
  rw [g32p_row43_traceCoefficients_056]
  decide +kernel

theorem g32p_row43_traceCoefficients_058 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 58 = [6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_058 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 58) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 58) (g32p_literalTraceValue 42 58)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_058]
  decide +kernel

theorem g32p_row43_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 59 = [4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 59) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 59) (g32p_literalTraceValue 42 59)
      [1, -1, 1] [432, 432] = true := by
  rw [g32p_row43_traceCoefficients_059]
  decide +kernel

theorem g32p_row43_traceCoefficients_061 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 61 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_061 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 61) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 61) (g32p_literalTraceValue 42 61)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_061]
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

theorem g32p_row43_traceCoefficients_063 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 63 = [0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_063 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 63) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 63) (g32p_literalTraceValue 42 63)
      [1, -1, 1] [432, 432] = true := by
  rw [g32p_row43_traceCoefficients_063]
  decide +kernel

theorem g32p_row43_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 64 = [0, 0, 4, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 64) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 64) (g32p_literalTraceValue 42 64)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_064]
  decide +kernel

theorem g32p_row43_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 65 = [0, 1, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 65) (g32p_literalTraceValue 42 65)
      [1, -1, 1] [0, 1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_065]
  decide +kernel

theorem g32p_row43_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 66 = [0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 66) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 66) (g32p_literalTraceValue 42 66)
      [1, -1, 1] [0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_066]
  decide +kernel

theorem g32p_row43_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 67 = [0, 0, 5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 67) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 67) (g32p_literalTraceValue 42 67)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_067]
  decide +kernel

theorem g32p_row43_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 71 = [4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 71) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 71) (g32p_literalTraceValue 42 71)
      [1, -1, 1] [432, 432] = true := by
  rw [g32p_row43_traceCoefficients_071]
  decide +kernel

theorem g32p_row43_traceCoefficients_072 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 72 = [0, 0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_072 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 72) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 72) (g32p_literalTraceValue 42 72)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_072]
  decide +kernel

theorem g32p_row43_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 74 = [0, 0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 74) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 74) (g32p_literalTraceValue 42 74)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_074]
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

theorem g32p_row43_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 75 = [0, 0, 0, 8] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 75) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 75) (g32p_literalTraceValue 42 75)
      [1, -1, 1] [2592, 2592] = true := by
  rw [g32p_row43_traceCoefficients_075]
  decide +kernel

theorem g32p_row43_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 76 = [0, 0, 0, 0, 5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 76) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 76) (g32p_literalTraceValue 42 76)
      [1, -1, 1] [19440, 19440, 19440] = true := by
  rw [g32p_row43_traceCoefficients_076]
  decide +kernel

theorem g32p_row43_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 77 = [0, 1, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 77) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 77) (g32p_literalTraceValue 42 77)
      [1, -1, 1] [1296, 1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_077]
  decide +kernel

theorem g32p_row43_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 78 = [0, 0, 4, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 78) (g32p_literalTraceValue 42 78)
      [1, -1, 1] [2592, 2592, 2592] = true := by
  rw [g32p_row43_traceCoefficients_078]
  decide +kernel

theorem g32p_row43_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 79 = [0, 0, 4, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 79) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 79) (g32p_literalTraceValue 42 79)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_079]
  decide +kernel

theorem g32p_row43_traceCoefficients_080 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 80 = [0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_080 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 80) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 80) (g32p_literalTraceValue 42 80)
      [1, -1, 1] [432, 432] = true := by
  rw [g32p_row43_traceCoefficients_080]
  decide +kernel

theorem g32p_row43_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 81 = [1, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 81) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 81) (g32p_literalTraceValue 42 81)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_081]
  decide +kernel

theorem g32p_row43_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 82 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 82) (g32p_literalTraceValue 42 82)
      [1, -1, 1] [0, 0, 1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_082]
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

theorem g32p_row43_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 83 = [0, 0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 83) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 83) (g32p_literalTraceValue 42 83)
      [1, -1, 1] [0, 0, 1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_083]
  decide +kernel

theorem g32p_row43_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 84 = [0, 0, 0, 0, 0, 8] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 84) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 84) (g32p_literalTraceValue 42 84)
      [1, -1, 1] [0, 0, 2592, 2592] = true := by
  rw [g32p_row43_traceCoefficients_084]
  decide +kernel

theorem g32p_row43_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 85 = [0, 1, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 85) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 85) (g32p_literalTraceValue 42 85)
      [1, -1, 1] [1296, 1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_085]
  decide +kernel

theorem g32p_row43_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 86 = [0, 0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 86) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 86) (g32p_literalTraceValue 42 86)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row43_traceCoefficients_086]
  decide +kernel

theorem g32p_row43_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 87 = [0, 0, 5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 87) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 87) (g32p_literalTraceValue 42 87)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_087]
  decide +kernel

theorem g32p_row43_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 88 = [0, 0, 0, 0, 0, 5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 88) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 88) (g32p_literalTraceValue 42 88)
      [1, -1, 1] [0, 0, 19440, 19440] = true := by
  rw [g32p_row43_traceCoefficients_088]
  decide +kernel

theorem g32p_row43_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 89 = [1, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 89) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 89) (g32p_literalTraceValue 42 89)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_089]
  decide +kernel

theorem g32p_row43_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 90 = [0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 90) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 90) (g32p_literalTraceValue 42 90)
      [1, -1, 1] [1728, 1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_090]
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

theorem g32p_row43_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 91 = [0, 0, 1, 0, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 91) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 91) (g32p_literalTraceValue 42 91)
      [1, -1, 1] [0, 0, 1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_091]
  decide +kernel

theorem g32p_row43_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 92 = [0, 0, 0, 4, 0, 4] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 92) (g32p_literalTraceValue 42 92)
      [1, -1, 1] [2592, 2592, 2592, 2592] = true := by
  rw [g32p_row43_traceCoefficients_092]
  decide +kernel

theorem g32p_row43_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 93 = [0, 0, 0, 5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 93) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 93) (g32p_literalTraceValue 42 93)
      [1, -1, 1] [19440, 19440] = true := by
  rw [g32p_row43_traceCoefficients_093]
  decide +kernel

theorem g32p_row43_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 94 = [0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 94) (g32p_literalTraceValue 42 94)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row43_traceCoefficients_094]
  decide +kernel

theorem g32p_row43_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 95 = [0, 0, 0, 0, 0, 5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 95) (g32p_literalTraceValue 42 95)
      [1, -1, 1] [0, 0, 19440, 19440] = true := by
  rw [g32p_row43_traceCoefficients_095]
  decide +kernel

theorem g32p_row43_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 96 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 96) (g32p_literalTraceValue 42 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row43_traceCoefficients_096]
  decide +kernel

theorem g32p_row43_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 97 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 97) (g32p_literalTraceValue 42 97)
      [1, -1, 1] [0, 0, 155520, 155520] = true := by
  rw [g32p_row43_traceCoefficients_097]
  decide +kernel

theorem g32p_row43_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 98 = [0, 0, 0, 5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 98) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 98) (g32p_literalTraceValue 42 98)
      [1, -1, 1] [19440, 19440] = true := by
  rw [g32p_row43_traceCoefficients_098]
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

theorem g32p_row43_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 99 = [0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 99) (g32p_literalTraceValue 42 99)
      [1, -1, 1] [155520, 155520] = true := by
  rw [g32p_row43_traceCoefficients_099]
  decide +kernel

theorem g32p_row43_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 100 = [0, 0, 0, 0, 5] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 100) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 100) (g32p_literalTraceValue 42 100)
      [1, -1, 1] [19440, 19440, 19440] = true := by
  rw [g32p_row43_traceCoefficients_100]
  decide +kernel

theorem g32p_row43_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row43_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) 101) (g32p_literalTraceValue 42 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row43_traceCoefficients_101]
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

def g32p_row43_generatorIndex : Fin 8 → Fin 408 :=
  ![42, 93, 144, 195, 288, 289, 390, 391]

theorem g32p_row43_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup24_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 42 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 42 g32p_row43_supplierClass
    g32p_row43_supplierClass_isConj g32p_supplierGroup24_support g32p_row43_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row43_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup24_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row43_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 42 c false (g32p_row43_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 42 c true (g32p_row43_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 42 c false (g32p_row43_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 42 c true (g32p_row43_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 42 c false (g32p_row43_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 42 c false (g32p_row43_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 42 c true (g32p_row43_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 42 c true (g32p_row43_coinduced_zero c hc true) 3

theorem g32p_row43_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row43_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row43_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row43_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row43_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row43_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row43_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row43_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row43_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row43_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row43_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row43_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row43_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup24_support →
      g32p_literalTraceValue (g32p_row43_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row43_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup24_support) :
    g32p_literalTraceValue (g32p_row43_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup24_support →
    g32p_literalTraceValue (g32p_row43_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row43_zeroTrace_block_00 r k
  · exact g32p_row43_zeroTrace_block_01 r k
  · exact g32p_row43_zeroTrace_block_02 r k
  · exact g32p_row43_zeroTrace_block_03 r k
  · exact g32p_row43_zeroTrace_block_04 r k
  · exact g32p_row43_zeroTrace_block_05 r k
  · exact g32p_row43_zeroTrace_block_06 r k

theorem g32p_row43_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup24_support) :
    (g32p_recordedInductionGenerators (g32p_row43_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row43_generatorIndex k) c) := by
  rw [g32p_row43_recordedGenerator_zero c hc k, g32p_row43_zeroTrace_arithmetic c k hc]
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

def g32p_row43_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [432, 432] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [432, 432])) else (if i.val < 10 then [] else (if i.val < 11 then [0, 0, 432, 432] else [2592, 2592, 2592])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [0, 432, 432] else (if i.val < 17 then [] else [0, 0, 432, 432]))) else (if i.val < 21 then (if i.val < 19 then [1728, 1728] else (if i.val < 20 then [-1296, 432, 432] else [432, 432, 432])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [0, 0, 1728, 1728] else [-2592, 0, 2592, 2592]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [0, 432, 432] else (if i.val < 27 then [] else [-432])) else (if i.val < 29 then [-19440] else (if i.val < 30 then [0, 0, 432, 432] else []))) else (if i.val < 34 then (if i.val < 32 then [-1728] else (if i.val < 33 then [-2592] else [])) else (if i.val < 36 then (if i.val < 35 then [] else [2592, 2592, 2592]) else (if i.val < 37 then [] else [-155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [432, 432])) else (if i.val < 42 then [-432] else (if i.val < 43 then [] else [0, 432, 432]))) else (if i.val < 47 then (if i.val < 45 then [-19440] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [432, 432])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [-1296, 432, 432] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [432, 432, 432] else [0, 2592]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [432, 432])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [432, 432] else (if i.val < 65 then [0, 0, 432, 432] else [0, 1728, 1728])) else (if i.val < 67 then [0, 432, 432] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [432, 432])) else (if i.val < 74 then (if i.val < 73 then [0, 0, 432, 432] else []) else (if i.val < 75 then [0, 0, 432, 432] else [2592, 2592]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [19440, 19440, 19440] else (if i.val < 78 then [1296, 1728, 1728] else [2592, 2592, 2592])) else (if i.val < 80 then [0, 0, 432, 432] else (if i.val < 81 then [432, 432] else [1728, 1728]))) else (if i.val < 85 then (if i.val < 83 then [0, 0, 1728, 1728] else (if i.val < 84 then [0, 0, 1728, 1728] else [0, 0, 2592, 2592])) else (if i.val < 87 then (if i.val < 86 then [1296, 1728, 1728] else [0, 0, 432, 432]) else (if i.val < 88 then [] else [0, 0, 19440, 19440])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [1728, 1728] else (if i.val < 91 then [1728, 1728, 1728] else [0, 0, 1728, 1728])) else (if i.val < 93 then [2592, 2592, 2592, 2592] else (if i.val < 94 then [19440, 19440] else [1728, 1728]))) else (if i.val < 98 then (if i.val < 96 then [0, 0, 19440, 19440] else (if i.val < 97 then [] else [0, 0, 155520, 155520])) else (if i.val < 100 then (if i.val < 99 then [19440, 19440] else [155520, 155520]) else (if i.val < 101 then [19440, 19440, 19440] else [155520, 155520, 155520])))))))

theorem g32p_row43_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup24_support) :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) c) (g32p_literalTraceValue 42 c)
      [1, -1, 1] (g32p_row43_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row43_tracePolynomial_000
  · exact g32p_row43_tracePolynomial_001
  · exact g32p_row43_tracePolynomial_002
  · exact g32p_row43_tracePolynomial_003
  · exact g32p_row43_tracePolynomial_004
  · exact g32p_row43_tracePolynomial_005
  · exact g32p_row43_tracePolynomial_006
  · exact g32p_row43_tracePolynomial_007
  · exact g32p_row43_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_010
  · exact g32p_row43_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_017
  · exact g32p_row43_tracePolynomial_018
  · exact g32p_row43_tracePolynomial_019
  · exact g32p_row43_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_023
  · exact g32p_row43_tracePolynomial_024
  · exact g32p_row43_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_027
  · exact g32p_row43_tracePolynomial_028
  · exact g32p_row43_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_031
  · exact g32p_row43_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_040
  · exact g32p_row43_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_043
  · exact g32p_row43_tracePolynomial_044
  · exact g32p_row43_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_048
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_050
  · exact g32p_row43_tracePolynomial_051
  · exact g32p_row43_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_055
  · exact g32p_row43_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_058
  · exact g32p_row43_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_061
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_063
  · exact g32p_row43_tracePolynomial_064
  · exact g32p_row43_tracePolynomial_065
  · exact g32p_row43_tracePolynomial_066
  · exact g32p_row43_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_071
  · exact g32p_row43_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row43_tracePolynomial_074
  · exact g32p_row43_tracePolynomial_075
  · exact g32p_row43_tracePolynomial_076
  · exact g32p_row43_tracePolynomial_077
  · exact g32p_row43_tracePolynomial_078
  · exact g32p_row43_tracePolynomial_079
  · exact g32p_row43_tracePolynomial_080
  · exact g32p_row43_tracePolynomial_081
  · exact g32p_row43_tracePolynomial_082
  · exact g32p_row43_tracePolynomial_083
  · exact g32p_row43_tracePolynomial_084
  · exact g32p_row43_tracePolynomial_085
  · exact g32p_row43_tracePolynomial_086
  · exact g32p_row43_tracePolynomial_087
  · exact g32p_row43_tracePolynomial_088
  · exact g32p_row43_tracePolynomial_089
  · exact g32p_row43_tracePolynomial_090
  · exact g32p_row43_tracePolynomial_091
  · exact g32p_row43_tracePolynomial_092
  · exact g32p_row43_tracePolynomial_093
  · exact g32p_row43_tracePolynomial_094
  · exact g32p_row43_tracePolynomial_095
  · exact g32p_row43_tracePolynomial_096
  · exact g32p_row43_tracePolynomial_097
  · exact g32p_row43_tracePolynomial_098
  · exact g32p_row43_tracePolynomial_099
  · exact g32p_row43_tracePolynomial_100
  · exact g32p_row43_tracePolynomial_101

theorem g32p_row43_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 42 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 42 c) := by
  by_cases hc : c ∈ g32p_supplierGroup24_support
  · have hclass (j : Fin 432) :
        IsConj (g32p_literalRepresentative c) (g32p_row33_groupEquiv j : g32p_G) ↔
          g32p_row43_supplierClassifier j = c := by
      simpa only [g32p_row43_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row43_supplierClass_iff (g32p_row33_groupEquiv j) c
    have hχ (j : Fin 432) :
        (g32p_recordedSupplierCharacters 42 (g32p_row33_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row43_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 42 (show (g32p_recordedSuppliers 42).H from g32p_row33_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row43_characterValues (g32p_row33_groupEquiv.symm (g32p_row33_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 42).H (g32p_recordedSupplierCharacters 42)
      (g32p_literalRepresentative c) g32p_row33_groupEquiv g32p_row43_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row43_characterValues j)).val) c 6 432
      (g32p_literalCentralizer c) (g32p_literalTraceValue 42 c) [1, -1, 1]
      (g32p_row43_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row43_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 42)))
      (g32p_row43_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row43_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row43_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
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

theorem g32p_row43_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
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

theorem g32p_row43_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
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

theorem g32p_row43_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
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

theorem g32p_row43_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
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

theorem g32p_row43_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row43_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row43_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 42 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
