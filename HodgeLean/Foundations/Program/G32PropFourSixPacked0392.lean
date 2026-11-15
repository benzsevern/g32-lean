import HodgeLean.Foundations.Program.G32PropFourSixPacked0391
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

theorem g32p_row23_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 0) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 0) (g32p_literalTraceValue 22 0)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_000]
  decide +kernel

theorem g32p_row23_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 1 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 1) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 1) (g32p_literalTraceValue 22 1)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_001]
  decide +kernel

theorem g32p_row23_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 2 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 2) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 2) (g32p_literalTraceValue 22 2)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row23_traceCoefficients_002]
  decide +kernel

theorem g32p_row23_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 3 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 3) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 3) (g32p_literalTraceValue 22 3)
      [1, 1, 1] [432] = true := by
  rw [g32p_row23_traceCoefficients_003]
  decide +kernel

theorem g32p_row23_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 4 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 4) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 4) (g32p_literalTraceValue 22 4)
      [1, 1, 1] [648] = true := by
  rw [g32p_row23_traceCoefficients_004]
  decide +kernel

theorem g32p_row23_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 6 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 6) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 6) (g32p_literalTraceValue 22 6)
      [1, 1, 1] [324] = true := by
  rw [g32p_row23_traceCoefficients_006]
  decide +kernel

theorem g32p_row23_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 8 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 8) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 8) (g32p_literalTraceValue 22 8)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_008]
  decide +kernel

theorem g32p_row23_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 10 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 10) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 10) (g32p_literalTraceValue 22 10)
      [1, 1, 1] [108] = true := by
  rw [g32p_row23_traceCoefficients_010]
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

theorem g32p_row23_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 11 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 11) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 11) (g32p_literalTraceValue 22 11)
      [1, 1, 1] [648] = true := by
  rw [g32p_row23_traceCoefficients_011]
  decide +kernel

theorem g32p_row23_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 15 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 15) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 15) (g32p_literalTraceValue 22 15)
      [1, 1, 1] [108] = true := by
  rw [g32p_row23_traceCoefficients_015]
  decide +kernel

theorem g32p_row23_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 18 = [2] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 18) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 18) (g32p_literalTraceValue 22 18)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_018]
  decide +kernel

theorem g32p_row23_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 19 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 19) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 19) (g32p_literalTraceValue 22 19)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_019]
  decide +kernel

theorem g32p_row23_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 23 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 23) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 23) (g32p_literalTraceValue 22 23)
      [1, 1, 1] [432] = true := by
  rw [g32p_row23_traceCoefficients_023]
  decide +kernel

theorem g32p_row23_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 24 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 24) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 24) (g32p_literalTraceValue 22 24)
      [1, 1, 1] [648] = true := by
  rw [g32p_row23_traceCoefficients_024]
  decide +kernel

theorem g32p_row23_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 25 = [0, 2] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 25) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 25) (g32p_literalTraceValue 22 25)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_025]
  decide +kernel

theorem g32p_row23_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 28 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 28) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 28) (g32p_literalTraceValue 22 28)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row23_traceCoefficients_028]
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

theorem g32p_row23_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 29 = [0, 0, 2] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 29) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 29) (g32p_literalTraceValue 22 29)
      [1, 1, 1] [216] = true := by
  rw [g32p_row23_traceCoefficients_029]
  decide +kernel

theorem g32p_row23_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 32 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 32) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 32) (g32p_literalTraceValue 22 32)
      [1, 1, 1] [324] = true := by
  rw [g32p_row23_traceCoefficients_032]
  decide +kernel

theorem g32p_row23_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 35 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 35) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 35) (g32p_literalTraceValue 22 35)
      [1, 1, 1] [324] = true := by
  rw [g32p_row23_traceCoefficients_035]
  decide +kernel

theorem g32p_row23_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 37 = [1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 37) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 37) (g32p_literalTraceValue 22 37)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_037]
  decide +kernel

theorem g32p_row23_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 40 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 40) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 40) (g32p_literalTraceValue 22 40)
      [1, 1, 1] [108] = true := by
  rw [g32p_row23_traceCoefficients_040]
  decide +kernel

theorem g32p_row23_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 43 = [0, 0, 2] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 43) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 43) (g32p_literalTraceValue 22 43)
      [1, 1, 1] [216] = true := by
  rw [g32p_row23_traceCoefficients_043]
  decide +kernel

theorem g32p_row23_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 44 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 44) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 44) (g32p_literalTraceValue 22 44)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_044]
  decide +kernel

theorem g32p_row23_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 45 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 45) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 45) (g32p_literalTraceValue 22 45)
      [1, 1, 1] [324] = true := by
  rw [g32p_row23_traceCoefficients_045]
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

theorem g32p_row23_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 50 = [0, 0, 2] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 50) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 50) (g32p_literalTraceValue 22 50)
      [1, 1, 1] [216] = true := by
  rw [g32p_row23_traceCoefficients_050]
  decide +kernel

theorem g32p_row23_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 51 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 51) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 51) (g32p_literalTraceValue 22 51)
      [1, 1, 1] [432] = true := by
  rw [g32p_row23_traceCoefficients_051]
  decide +kernel

theorem g32p_row23_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 56 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 56) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 56) (g32p_literalTraceValue 22 56)
      [1, 1, 1] [648] = true := by
  rw [g32p_row23_traceCoefficients_056]
  decide +kernel

theorem g32p_row23_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 59 = [0, 2] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 59) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 59) (g32p_literalTraceValue 22 59)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_059]
  decide +kernel

theorem g32p_row23_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 64 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 64) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 64) (g32p_literalTraceValue 22 64)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_064]
  decide +kernel

theorem g32p_row23_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 65 = [2] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 65) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 65) (g32p_literalTraceValue 22 65)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_065]
  decide +kernel

theorem g32p_row23_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 66 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 66) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 66) (g32p_literalTraceValue 22 66)
      [1, 1, 1] [108] = true := by
  rw [g32p_row23_traceCoefficients_066]
  decide +kernel

theorem g32p_row23_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 67 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 67) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 67) (g32p_literalTraceValue 22 67)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row23_traceCoefficients_067]
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

theorem g32p_row23_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 71 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 71) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 71) (g32p_literalTraceValue 22 71)
      [1, 1, 1] [108] = true := by
  rw [g32p_row23_traceCoefficients_071]
  decide +kernel

theorem g32p_row23_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 74 = [0, 2] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 74) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 74) (g32p_literalTraceValue 22 74)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_074]
  decide +kernel

theorem g32p_row23_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 75 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 75) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 75) (g32p_literalTraceValue 22 75)
      [1, 1, 1] [324] = true := by
  rw [g32p_row23_traceCoefficients_075]
  decide +kernel

theorem g32p_row23_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 76 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 76) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 76) (g32p_literalTraceValue 22 76)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_076]
  decide +kernel

theorem g32p_row23_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 77 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 77) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 77) (g32p_literalTraceValue 22 77)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_077]
  decide +kernel

theorem g32p_row23_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 78 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 78) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 78) (g32p_literalTraceValue 22 78)
      [1, 1, 1] [648] = true := by
  rw [g32p_row23_traceCoefficients_078]
  decide +kernel

theorem g32p_row23_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 79 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 79) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 79) (g32p_literalTraceValue 22 79)
      [1, 1, 1] [432] = true := by
  rw [g32p_row23_traceCoefficients_079]
  decide +kernel

theorem g32p_row23_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 81 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 81) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 81) (g32p_literalTraceValue 22 81)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_081]
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

theorem g32p_row23_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 82 = [2] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 82) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 82) (g32p_literalTraceValue 22 82)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_082]
  decide +kernel

theorem g32p_row23_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 84 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 84) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 84) (g32p_literalTraceValue 22 84)
      [1, 1, 1] [324] = true := by
  rw [g32p_row23_traceCoefficients_084]
  decide +kernel

theorem g32p_row23_traceCoefficients_085 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 85 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 85) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 85) (g32p_literalTraceValue 22 85)
      [1, 1, 1] [432] = true := by
  rw [g32p_row23_traceCoefficients_085]
  decide +kernel

theorem g32p_row23_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 86 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 86) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 86) (g32p_literalTraceValue 22 86)
      [1, 1, 1] [108] = true := by
  rw [g32p_row23_traceCoefficients_086]
  decide +kernel

theorem g32p_row23_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 87 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 87) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 87) (g32p_literalTraceValue 22 87)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_087]
  decide +kernel

theorem g32p_row23_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 88 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 88) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 88) (g32p_literalTraceValue 22 88)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_088]
  decide +kernel

theorem g32p_row23_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 89 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 89) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 89) (g32p_literalTraceValue 22 89)
      [1, 1, 1] [432] = true := by
  rw [g32p_row23_traceCoefficients_089]
  decide +kernel

theorem g32p_row23_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 91 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 91) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 91) (g32p_literalTraceValue 22 91)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_091]
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

theorem g32p_row23_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 92 = [0, 1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 92) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 92) (g32p_literalTraceValue 22 92)
      [1, 1, 1] [648] = true := by
  rw [g32p_row23_traceCoefficients_092]
  decide +kernel

theorem g32p_row23_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 93 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 93) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 93) (g32p_literalTraceValue 22 93)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row23_traceCoefficients_093]
  decide +kernel

theorem g32p_row23_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 95 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 95) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 95) (g32p_literalTraceValue 22 95)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row23_traceCoefficients_095]
  decide +kernel

theorem g32p_row23_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 96 = [1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 96) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 96) (g32p_literalTraceValue 22 96)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_096]
  decide +kernel

theorem g32p_row23_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 97 = [1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 97) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 97) (g32p_literalTraceValue 22 97)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_097]
  decide +kernel

theorem g32p_row23_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 98 = [1, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 98) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 98) (g32p_literalTraceValue 22 98)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_098]
  decide +kernel

theorem g32p_row23_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 99 = [1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 99) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 99) (g32p_literalTraceValue 22 99)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_099]
  decide +kernel

theorem g32p_row23_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 100 = [1, 0, 1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 100) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 100) (g32p_literalTraceValue 22 100)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row23_traceCoefficients_100]
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

theorem g32p_row23_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 101 = [1] := by
  decide +kernel

theorem g32p_row23_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer 101) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) 101) (g32p_literalTraceValue 22 101)
      [1, 1, 1] [] = true := by
  rw [g32p_row23_traceCoefficients_101]
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

def g32p_row23_generatorIndex : Fin 8 → Fin 408 :=
  ![22, 73, 124, 175, 248, 249, 350, 351]

theorem g32p_row23_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup18_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 22 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 22 g32p_row23_supplierClass
    g32p_row23_supplierClass_isConj g32p_supplierGroup18_support g32p_row23_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row23_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup18_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row23_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 22 c false (g32p_row23_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 22 c true (g32p_row23_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 22 c false (g32p_row23_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 22 c true (g32p_row23_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 22 c false (g32p_row23_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 22 c false (g32p_row23_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 22 c true (g32p_row23_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 22 c true (g32p_row23_coinduced_zero c hc true) 3

theorem g32p_row23_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup18_support →
      g32p_literalTraceValue (g32p_row23_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row23_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup18_support →
      g32p_literalTraceValue (g32p_row23_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row23_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup18_support →
      g32p_literalTraceValue (g32p_row23_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row23_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup18_support →
      g32p_literalTraceValue (g32p_row23_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row23_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup18_support →
      g32p_literalTraceValue (g32p_row23_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row23_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup18_support →
      g32p_literalTraceValue (g32p_row23_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row23_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup18_support →
      g32p_literalTraceValue (g32p_row23_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row23_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup18_support) :
    g32p_literalTraceValue (g32p_row23_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup18_support →
    g32p_literalTraceValue (g32p_row23_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row23_zeroTrace_block_00 r k
  · exact g32p_row23_zeroTrace_block_01 r k
  · exact g32p_row23_zeroTrace_block_02 r k
  · exact g32p_row23_zeroTrace_block_03 r k
  · exact g32p_row23_zeroTrace_block_04 r k
  · exact g32p_row23_zeroTrace_block_05 r k
  · exact g32p_row23_zeroTrace_block_06 r k

theorem g32p_row23_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup18_support) :
    (g32p_recordedInductionGenerators (g32p_row23_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row23_generatorIndex k) c) := by
  rw [g32p_row23_recordedGenerator_zero c hc k, g32p_row23_zeroTrace_arithmetic c k hc]
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

def g32p_row23_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [3888])) else (if i.val < 4 then [432] else (if i.val < 5 then [648] else []))) else (if i.val < 9 then (if i.val < 7 then [324] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [108] else [648])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [108] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [432] else [648]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [3888] else (if i.val < 30 then [216] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [324] else [])) else (if i.val < 36 then (if i.val < 35 then [] else [324]) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [108])) else (if i.val < 42 then [] else (if i.val < 43 then [] else [216]))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [324] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [216])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [432] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else [648]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [108] else (if i.val < 68 then [3888] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [108])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else [324]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [648])) else (if i.val < 80 then [432] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [324])) else (if i.val < 87 then (if i.val < 86 then [432] else [108]) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [432] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [648] else (if i.val < 94 then [3888] else []))) else (if i.val < 98 then (if i.val < 96 then [3888] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [3888] else [])))))))

theorem g32p_row23_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup18_support) :
    g32p_supplierTracePolynomialCheck 108 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) c) (g32p_literalTraceValue 22 c)
      [1, 1, 1] (g32p_row23_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row23_tracePolynomial_000
  · exact g32p_row23_tracePolynomial_001
  · exact g32p_row23_tracePolynomial_002
  · exact g32p_row23_tracePolynomial_003
  · exact g32p_row23_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_010
  · exact g32p_row23_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_018
  · exact g32p_row23_tracePolynomial_019
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_023
  · exact g32p_row23_tracePolynomial_024
  · exact g32p_row23_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_028
  · exact g32p_row23_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_040
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_043
  · exact g32p_row23_tracePolynomial_044
  · exact g32p_row23_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_050
  · exact g32p_row23_tracePolynomial_051
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_064
  · exact g32p_row23_tracePolynomial_065
  · exact g32p_row23_tracePolynomial_066
  · exact g32p_row23_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_071
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_074
  · exact g32p_row23_tracePolynomial_075
  · exact g32p_row23_tracePolynomial_076
  · exact g32p_row23_tracePolynomial_077
  · exact g32p_row23_tracePolynomial_078
  · exact g32p_row23_tracePolynomial_079
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_081
  · exact g32p_row23_tracePolynomial_082
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_084
  · exact g32p_row23_tracePolynomial_085
  · exact g32p_row23_tracePolynomial_086
  · exact g32p_row23_tracePolynomial_087
  · exact g32p_row23_tracePolynomial_088
  · exact g32p_row23_tracePolynomial_089
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_091
  · exact g32p_row23_tracePolynomial_092
  · exact g32p_row23_tracePolynomial_093
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup18_support) hc)
  · exact g32p_row23_tracePolynomial_095
  · exact g32p_row23_tracePolynomial_096
  · exact g32p_row23_tracePolynomial_097
  · exact g32p_row23_tracePolynomial_098
  · exact g32p_row23_tracePolynomial_099
  · exact g32p_row23_tracePolynomial_100
  · exact g32p_row23_tracePolynomial_101

theorem g32p_row23_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 22 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 22 c) := by
  by_cases hc : c ∈ g32p_supplierGroup18_support
  · have hclass (j : Fin 108) :
        IsConj (g32p_literalRepresentative c) (g32p_row23_groupEquiv j : g32p_G) ↔
          g32p_row23_supplierClassifier j = c := by
      simpa only [g32p_row23_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row23_supplierClass_iff (g32p_row23_groupEquiv j) c
    have hχ (j : Fin 108) :
        (g32p_recordedSupplierCharacters 22 (g32p_row23_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row23_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 22 (show (g32p_recordedSuppliers 22).H from g32p_row23_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row23_characterValues (g32p_row23_groupEquiv.symm (g32p_row23_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 22).H (g32p_recordedSupplierCharacters 22)
      (g32p_literalRepresentative c) g32p_row23_groupEquiv g32p_row23_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row23_characterValues j)).val) c 3 108
      (g32p_literalCentralizer c) (g32p_literalTraceValue 22 c) [1, 1, 1]
      (g32p_row23_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row23_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 22)))
      (g32p_row23_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row23_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row23_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
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

theorem g32p_row23_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
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

theorem g32p_row23_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
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

theorem g32p_row23_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
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

theorem g32p_row23_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
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

theorem g32p_row23_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
