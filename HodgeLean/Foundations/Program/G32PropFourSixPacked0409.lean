import HodgeLean.Foundations.Program.G32PropFourSixPacked0408
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow31
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row30_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 0) (g32p_literalTraceValue 29 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row30_traceCoefficients_000]
  decide +kernel

theorem g32p_row30_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 6 = [24, 0, 3, 0, 3] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 6) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 6) (g32p_literalTraceValue 29 6)
      [1, -1, 1] [972, 972, 972] = true := by
  rw [g32p_row30_traceCoefficients_006]
  decide +kernel

theorem g32p_row30_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 18 = [9, 0, 0, 9] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 18) (g32p_literalTraceValue 29 18)
      [1, -1, 1] [15552, 15552] = true := by
  rw [g32p_row30_traceCoefficients_018]
  decide +kernel

theorem g32p_row30_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 19 = [9, 0, 0, 0, 0, 9] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 19) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 19) (g32p_literalTraceValue 29 19)
      [1, -1, 1] [0, 0, 3888, 3888] = true := by
  rw [g32p_row30_traceCoefficients_019]
  decide +kernel

theorem g32p_row30_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 23 = [9, 9] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 23) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 23) (g32p_literalTraceValue 29 23)
      [1, -1, 1] [-3888] = true := by
  rw [g32p_row30_traceCoefficients_023]
  decide +kernel

theorem g32p_row30_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 24 = [0, 3, 0, 0, 0, 3] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 24) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 24) (g32p_literalTraceValue 29 24)
      [1, -1, 1] [-1944, 0, 1944, 1944] = true := by
  rw [g32p_row30_traceCoefficients_024]
  decide +kernel

theorem g32p_row30_traceCoefficients_039 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 39 = [0, 0, 0, 0, 0, 18] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_039 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 39) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 39) (g32p_literalTraceValue 29 39)
      [1, -1, 1] [0, 0, 972, 972] = true := by
  rw [g32p_row30_traceCoefficients_039]
  decide +kernel

theorem g32p_row30_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 40 = [0, 0, 0, 0, 9, 9] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 40) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 40) (g32p_literalTraceValue 29 40)
      [1, -1, 1] [972, 972, 1944, 972] = true := by
  rw [g32p_row30_traceCoefficients_040]
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

theorem g32p_row30_traceCoefficients_042 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 42 = [0, 0, 18] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_042 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 42) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 42) (g32p_literalTraceValue 29 42)
      [1, -1, 1] [] = true := by
  rw [g32p_row30_traceCoefficients_042]
  decide +kernel

theorem g32p_row30_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 43 = [0, 9, 0, 0, 9] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 43) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 43) (g32p_literalTraceValue 29 43)
      [1, -1, 1] [0, 972, 972] = true := by
  rw [g32p_row30_traceCoefficients_043]
  decide +kernel

theorem g32p_row30_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 44 = [0, 0, 0, 1, 0, 3] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 44) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 44) (g32p_literalTraceValue 29 44)
      [1, -1, 1] [3888, 3888, 11664, 11664] = true := by
  rw [g32p_row30_traceCoefficients_044]
  decide +kernel

theorem g32p_row30_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 67 = [1, 0, 0, 0, 3] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 67) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 67) (g32p_literalTraceValue 29 67)
      [1, -1, 1] [11664, 11664, 11664] = true := by
  rw [g32p_row30_traceCoefficients_067]
  decide +kernel

theorem g32p_row30_traceCoefficients_068 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 68 = [0, 0, 0, 0, 18] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_068 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 68) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 68) (g32p_literalTraceValue 29 68)
      [1, -1, 1] [972, 972, 972] = true := by
  rw [g32p_row30_traceCoefficients_068]
  decide +kernel

theorem g32p_row30_traceCoefficients_070 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 70 = [0, 18] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_070 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 70) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 70) (g32p_literalTraceValue 29 70)
      [1, -1, 1] [-972] = true := by
  rw [g32p_row30_traceCoefficients_070]
  decide +kernel

theorem g32p_row30_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 71 = [0, 9, 9] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 71) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 71) (g32p_literalTraceValue 29 71)
      [1, -1, 1] [-972] = true := by
  rw [g32p_row30_traceCoefficients_071]
  decide +kernel

theorem g32p_row30_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 74 = [0, 0, 9, 0, 0, 9] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 74) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 74) (g32p_literalTraceValue 29 74)
      [1, -1, 1] [0, 0, 972, 972] = true := by
  rw [g32p_row30_traceCoefficients_074]
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

theorem g32p_row30_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 75 = [0, 3, 0, 24, 0, 3] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 75) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 75) (g32p_literalTraceValue 29 75)
      [1, -1, 1] [6804, 7776, 972, 972] = true := by
  rw [g32p_row30_traceCoefficients_075]
  decide +kernel

theorem g32p_row30_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 76 = [1, 0, 3] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 76) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 76) (g32p_literalTraceValue 29 76)
      [1, -1, 1] [] = true := by
  rw [g32p_row30_traceCoefficients_076]
  decide +kernel

theorem g32p_row30_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 77 = [0, 0, 9, 9] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 77) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 77) (g32p_literalTraceValue 29 77)
      [1, -1, 1] [3888, 3888] = true := by
  rw [g32p_row30_traceCoefficients_077]
  decide +kernel

theorem g32p_row30_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 78 = [0, 0, 3, 0, 3] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 78) (g32p_literalTraceValue 29 78)
      [1, -1, 1] [1944, 1944, 1944] = true := by
  rw [g32p_row30_traceCoefficients_078]
  decide +kernel

theorem g32p_row30_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 79 = [0, 0, 0, 9, 9] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 79) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 79) (g32p_literalTraceValue 29 79)
      [1, -1, 1] [7776, 7776, 3888] = true := by
  rw [g32p_row30_traceCoefficients_079]
  decide +kernel

theorem g32p_row30_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 95 = [0, 3, 0, 1] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 95) (g32p_literalTraceValue 29 95)
      [1, -1, 1] [-7776, 3888] = true := by
  rw [g32p_row30_traceCoefficients_095]
  decide +kernel

theorem g32p_row30_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 99 = [0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row30_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) 99) (g32p_literalTraceValue 29 99)
      [1, -1, 1] [155520, 155520] = true := by
  rw [g32p_row30_traceCoefficients_099]
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

def g32p_row30_generatorIndex : Fin 8 → Fin 408 :=
  ![29, 80, 131, 182, 262, 263, 364, 365]

theorem g32p_row30_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup21_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 29 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 29 g32p_row30_supplierClass
    g32p_row30_supplierClass_isConj g32p_supplierGroup21_support g32p_row30_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row30_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup21_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row30_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 29 c false (g32p_row30_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 29 c true (g32p_row30_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 29 c false (g32p_row30_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 29 c true (g32p_row30_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 29 c false (g32p_row30_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 29 c false (g32p_row30_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 29 c true (g32p_row30_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 29 c true (g32p_row30_coinduced_zero c hc true) 3

theorem g32p_row30_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup21_support →
      g32p_literalTraceValue (g32p_row30_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row30_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup21_support →
      g32p_literalTraceValue (g32p_row30_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row30_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup21_support →
      g32p_literalTraceValue (g32p_row30_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row30_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup21_support →
      g32p_literalTraceValue (g32p_row30_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row30_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup21_support →
      g32p_literalTraceValue (g32p_row30_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row30_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup21_support →
      g32p_literalTraceValue (g32p_row30_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row30_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup21_support →
      g32p_literalTraceValue (g32p_row30_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row30_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup21_support) :
    g32p_literalTraceValue (g32p_row30_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup21_support →
    g32p_literalTraceValue (g32p_row30_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row30_zeroTrace_block_00 r k
  · exact g32p_row30_zeroTrace_block_01 r k
  · exact g32p_row30_zeroTrace_block_02 r k
  · exact g32p_row30_zeroTrace_block_03 r k
  · exact g32p_row30_zeroTrace_block_04 r k
  · exact g32p_row30_zeroTrace_block_05 r k
  · exact g32p_row30_zeroTrace_block_06 r k

theorem g32p_row30_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup21_support) :
    (g32p_recordedInductionGenerators (g32p_row30_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row30_generatorIndex k) c) := by
  rw [g32p_row30_recordedGenerator_zero c hc k, g32p_row30_zeroTrace_arithmetic c k hc]
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

def g32p_row30_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [972, 972, 972] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [15552, 15552] else (if i.val < 20 then [0, 0, 3888, 3888] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [-3888] else [-1944, 0, 1944, 1944]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [0, 0, 972, 972] else [972, 972, 1944, 972])) else (if i.val < 42 then [] else (if i.val < 43 then [] else [0, 972, 972]))) else (if i.val < 47 then (if i.val < 45 then [3888, 3888, 11664, 11664] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [11664, 11664, 11664] else [972, 972, 972]))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [-972] else [-972])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [0, 0, 972, 972] else [6804, 7776, 972, 972]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [3888, 3888] else [1944, 1944, 1944])) else (if i.val < 80 then [7776, 7776, 3888] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [-7776, 3888] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else [155520, 155520]) else (if i.val < 101 then [] else [])))))))

theorem g32p_row30_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup21_support) :
    g32p_supplierTracePolynomialCheck 324 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) c) (g32p_literalTraceValue 29 c)
      [1, -1, 1] (g32p_row30_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row30_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact g32p_row30_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact g32p_row30_tracePolynomial_018
  · exact g32p_row30_tracePolynomial_019
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact g32p_row30_tracePolynomial_023
  · exact g32p_row30_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact g32p_row30_tracePolynomial_039
  · exact g32p_row30_tracePolynomial_040
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact g32p_row30_tracePolynomial_042
  · exact g32p_row30_tracePolynomial_043
  · exact g32p_row30_tracePolynomial_044
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact g32p_row30_tracePolynomial_067
  · exact g32p_row30_tracePolynomial_068
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact g32p_row30_tracePolynomial_070
  · exact g32p_row30_tracePolynomial_071
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact g32p_row30_tracePolynomial_074
  · exact g32p_row30_tracePolynomial_075
  · exact g32p_row30_tracePolynomial_076
  · exact g32p_row30_tracePolynomial_077
  · exact g32p_row30_tracePolynomial_078
  · exact g32p_row30_tracePolynomial_079
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact g32p_row30_tracePolynomial_095
  · exact False.elim ((by decide : (96 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact g32p_row30_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup21_support) hc)
  · exact False.elim ((by decide : (101 : Fin 102) ∉ g32p_supplierGroup21_support) hc)

theorem g32p_row30_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 29 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 29 c) := by
  by_cases hc : c ∈ g32p_supplierGroup21_support
  · have hclass (j : Fin 324) :
        IsConj (g32p_literalRepresentative c) (g32p_row30_groupEquiv j : g32p_G) ↔
          g32p_row30_supplierClassifier j = c := by
      simpa only [g32p_row30_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row30_supplierClass_iff (g32p_row30_groupEquiv j) c
    have hχ (j : Fin 324) :
        (g32p_recordedSupplierCharacters 29 (g32p_row30_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row30_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 29 (show (g32p_recordedSuppliers 29).H from g32p_row30_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row30_characterValues (g32p_row30_groupEquiv.symm (g32p_row30_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 29).H (g32p_recordedSupplierCharacters 29)
      (g32p_literalRepresentative c) g32p_row30_groupEquiv g32p_row30_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row30_characterValues j)).val) c 6 324
      (g32p_literalCentralizer c) (g32p_literalTraceValue 29 c) [1, -1, 1]
      (g32p_row30_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row30_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 29)))
      (g32p_row30_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row30_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row30_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
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

theorem g32p_row30_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
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

theorem g32p_row30_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
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

theorem g32p_row30_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
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

theorem g32p_row30_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
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

theorem g32p_row30_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
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

theorem g32p_row30_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row30_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row30_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
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

theorem g32p_row30_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row30_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row30_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row30_variantArithmetic_00_0 r
  · exact g32p_row30_variantArithmetic_01_0 r
  · exact g32p_row30_variantArithmetic_02_0 r
  · exact g32p_row30_variantArithmetic_03_0 r
  · exact g32p_row30_variantArithmetic_04_0 r
  · exact g32p_row30_variantArithmetic_05_0 r
  · exact g32p_row30_variantArithmetic_06_0 r

theorem g32p_row30_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row30_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row30_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row30_variantArithmetic_00_1 r
  · exact g32p_row30_variantArithmetic_01_1 r
  · exact g32p_row30_variantArithmetic_02_1 r
  · exact g32p_row30_variantArithmetic_03_1 r
  · exact g32p_row30_variantArithmetic_04_1 r
  · exact g32p_row30_variantArithmetic_05_1 r
  · exact g32p_row30_variantArithmetic_06_1 r

theorem g32p_row30_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row30_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row30_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row30_variantArithmetic_00_2 r
  · exact g32p_row30_variantArithmetic_01_2 r
  · exact g32p_row30_variantArithmetic_02_2 r
  · exact g32p_row30_variantArithmetic_03_2 r
  · exact g32p_row30_variantArithmetic_04_2 r
  · exact g32p_row30_variantArithmetic_05_2 r
  · exact g32p_row30_variantArithmetic_06_2 r

theorem g32p_row30_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row30_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row30_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row30_variantArithmetic_00_3 r
  · exact g32p_row30_variantArithmetic_01_3 r
  · exact g32p_row30_variantArithmetic_02_3 r
  · exact g32p_row30_variantArithmetic_03_3 r
  · exact g32p_row30_variantArithmetic_04_3 r
  · exact g32p_row30_variantArithmetic_05_3 r
  · exact g32p_row30_variantArithmetic_06_3 r

theorem g32p_row30_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row30_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row30_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row30_variantArithmetic_00_4 r
  · exact g32p_row30_variantArithmetic_01_4 r
  · exact g32p_row30_variantArithmetic_02_4 r
  · exact g32p_row30_variantArithmetic_03_4 r
  · exact g32p_row30_variantArithmetic_04_4 r
  · exact g32p_row30_variantArithmetic_05_4 r
  · exact g32p_row30_variantArithmetic_06_4 r

theorem g32p_row30_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row30_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row30_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row30_variantArithmetic_00_5 r
  · exact g32p_row30_variantArithmetic_01_5 r
  · exact g32p_row30_variantArithmetic_02_5 r
  · exact g32p_row30_variantArithmetic_03_5 r
  · exact g32p_row30_variantArithmetic_04_5 r
  · exact g32p_row30_variantArithmetic_05_5 r
  · exact g32p_row30_variantArithmetic_06_5 r

theorem g32p_row30_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row30_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row30_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row30_variantArithmetic_00_6 r
  · exact g32p_row30_variantArithmetic_01_6 r
  · exact g32p_row30_variantArithmetic_02_6 r
  · exact g32p_row30_variantArithmetic_03_6 r
  · exact g32p_row30_variantArithmetic_04_6 r
  · exact g32p_row30_variantArithmetic_05_6 r
  · exact g32p_row30_variantArithmetic_06_6 r

theorem g32p_row30_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row30_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row30_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 29 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row30_variantArithmetic_00_7 r
  · exact g32p_row30_variantArithmetic_01_7 r
  · exact g32p_row30_variantArithmetic_02_7 r
  · exact g32p_row30_variantArithmetic_03_7 r
  · exact g32p_row30_variantArithmetic_04_7 r
  · exact g32p_row30_variantArithmetic_05_7 r
  · exact g32p_row30_variantArithmetic_06_7 r

theorem g32p_row30_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row30_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row30_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 29 c _ (g32p_row30_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row30_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 29 c _ (g32p_row30_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row30_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 29 c _ (g32p_row30_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row30_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 29 c _ (g32p_row30_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row30_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 29 c _ (g32p_row30_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row30_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 29 c _ (g32p_row30_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row30_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 29 c _ (g32p_row30_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row30_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 29 c _ (g32p_row30_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row30_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup22_source : Fin 18 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (105, 126)) else (if i.val < 3 then (30, 150) else (0, 96))) else (if i.val < 6 then (if i.val < 5 then (116, 169) else (14, 66)) else (if i.val < 7 then (16, 48) else (if i.val < 8 then (59, 10) else (131, 183))))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then (0, 101) else (82, 82)) else (if i.val < 12 then (70, 196) else (4, 145))) else (if i.val < 15 then (if i.val < 14 then (62, 90) else (120, 62)) else (if i.val < 16 then (112, 2) else (if i.val < 17 then (57, 13) else (75, 78))))))

def g32p_supplierGroup22_classify : Fin 18 → Fin 102 :=
  fun i => (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 65) else (if i.val < 3 then 78 else 96)) else (if i.val < 6 then (if i.val < 5 then 59 else 78) else (if i.val < 7 then 18 else (if i.val < 8 then 11 else 29)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 101 else 74) else (if i.val < 12 then 11 else 82)) else (if i.val < 15 then (if i.val < 14 then 4 else 43) else (if i.val < 16 then 25 else (if i.val < 17 then 4 else 50)))))

def g32p_supplierGroup22_support : Finset (Fin 102) :=
  {0, 4, 11, 18, 25, 29, 43, 50, 59, 65, 74, 78, 82, 96, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup22_matrix_000 : ∀ r : Fin 16,
    g32p_row31_groupNodes (g32p_finBlockIndex 18 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup22_source (g32p_finBlockIndex 18 0 r)).1 (g32p_supplierGroup22_source (g32p_finBlockIndex 18 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup22_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup22_source (g32p_finBlockIndex 18 0 r)).1 (g32p_supplierGroup22_source (g32p_finBlockIndex 18 0 r)).2 =
      g32p_supplierGroup22_classify (g32p_finBlockIndex 18 0 r) := by
  decide +kernel

theorem g32p_supplierGroup22_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup22_classify (g32p_finBlockIndex 18 0 r) ∈ g32p_supplierGroup22_support := by
  decide +kernel

theorem g32p_supplierGroup22_matrix_001 : ∀ r : Fin 16,
    g32p_row31_groupNodes (g32p_finBlockIndex 18 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup22_source (g32p_finBlockIndex 18 1 r)).1 (g32p_supplierGroup22_source (g32p_finBlockIndex 18 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup22_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup22_source (g32p_finBlockIndex 18 1 r)).1 (g32p_supplierGroup22_source (g32p_finBlockIndex 18 1 r)).2 =
      g32p_supplierGroup22_classify (g32p_finBlockIndex 18 1 r) := by
  decide +kernel

theorem g32p_supplierGroup22_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup22_classify (g32p_finBlockIndex 18 1 r) ∈ g32p_supplierGroup22_support := by
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

theorem g32p_supplierGroup22_matrix (i : Fin 18) :
    g32p_row31_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup22_source i).1 (g32p_supplierGroup22_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row31_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup22_source i).1 (g32p_supplierGroup22_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup22_matrix_000 r
  · exact g32p_supplierGroup22_matrix_001 r

theorem g32p_supplierGroup22_class (i : Fin 18) :
    g32p_supplierForest_classes (g32p_supplierGroup22_source i).1 (g32p_supplierGroup22_source i).2 =
      g32p_supplierGroup22_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup22_source i).1 (g32p_supplierGroup22_source i).2 =
      g32p_supplierGroup22_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup22_class_000 r
  · exact g32p_supplierGroup22_class_001 r

theorem g32p_supplierGroup22_support_mem (i : Fin 18) :
    g32p_supplierGroup22_classify i ∈ g32p_supplierGroup22_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup22_classify i ∈ g32p_supplierGroup22_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup22_support_000 r
  · exact g32p_supplierGroup22_support_001 r

end HodgeLean.Foundations.Program

end
end
