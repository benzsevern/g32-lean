import HodgeLean.Foundations.Program.G32PropFourSixPacked0360
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixFiniteCharacter
import HodgeLean.Foundations.Program.G32PropFourSixPacked0187

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row12_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 67 = [1, 0, 0, 0, 3] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 67) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 67) (g32p_literalTraceValue 11 67)
      [1, -1, 1] [11664, 11664, 11664] = true := by
  rw [g32p_row12_traceCoefficients_067]
  decide +kernel

theorem g32p_row12_traceCoefficients_068 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 68 = [0, 0, 0, 0, 18] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_068 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 68) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 68) (g32p_literalTraceValue 11 68)
      [1, -1, 1] [972, 972, 972] = true := by
  rw [g32p_row12_traceCoefficients_068]
  decide +kernel

theorem g32p_row12_traceCoefficients_070 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 70 = [0, 18] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_070 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 70) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 70) (g32p_literalTraceValue 11 70)
      [1, -1, 1] [-972] = true := by
  rw [g32p_row12_traceCoefficients_070]
  decide +kernel

theorem g32p_row12_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 75 = [0, 3, 0, 24, 0, 3] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 75) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 75) (g32p_literalTraceValue 11 75)
      [1, -1, 1] [6804, 7776, 972, 972] = true := by
  rw [g32p_row12_traceCoefficients_075]
  decide +kernel

theorem g32p_row12_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 76 = [1, 0, 3] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 76) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 76) (g32p_literalTraceValue 11 76)
      [1, -1, 1] [] = true := by
  rw [g32p_row12_traceCoefficients_076]
  decide +kernel

theorem g32p_row12_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 78 = [0, 0, 3, 0, 3] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 78) (g32p_literalTraceValue 11 78)
      [1, -1, 1] [1944, 1944, 1944] = true := by
  rw [g32p_row12_traceCoefficients_078]
  decide +kernel

theorem g32p_row12_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 84 = [0, 3, 0, 3, 0, 24] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 84) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 84) (g32p_literalTraceValue 11 84)
      [1, -1, 1] [0, 972, 7776, 7776] = true := by
  rw [g32p_row12_traceCoefficients_084]
  decide +kernel

theorem g32p_row12_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 87 = [3, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 87) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 87) (g32p_literalTraceValue 11 87)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row12_traceCoefficients_087]
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

theorem g32p_row12_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 88 = [0, 1, 0, 3] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 88) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 88) (g32p_literalTraceValue 11 88)
      [1, -1, 1] [7776, 11664] = true := by
  rw [g32p_row12_traceCoefficients_088]
  decide +kernel

theorem g32p_row12_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 92 = [0, 0, 0, 3, 0, 3] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 92) (g32p_literalTraceValue 11 92)
      [1, -1, 1] [1944, 1944, 1944, 1944] = true := by
  rw [g32p_row12_traceCoefficients_092]
  decide +kernel

theorem g32p_row12_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 93 = [0, 1, 0, 0, 0, 3] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 93) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 93) (g32p_literalTraceValue 11 93)
      [1, -1, 1] [-3888, 0, 11664, 11664] = true := by
  rw [g32p_row12_traceCoefficients_093]
  decide +kernel

theorem g32p_row12_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 95 = [0, 3, 0, 1] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 95) (g32p_literalTraceValue 11 95)
      [1, -1, 1] [-7776, 3888] = true := by
  rw [g32p_row12_traceCoefficients_095]
  decide +kernel

theorem g32p_row12_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 96 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 96) (g32p_literalTraceValue 11 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row12_traceCoefficients_096]
  decide +kernel

theorem g32p_row12_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 97 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 97) (g32p_literalTraceValue 11 97)
      [1, -1, 1] [0, 0, 155520, 155520] = true := by
  rw [g32p_row12_traceCoefficients_097]
  decide +kernel

theorem g32p_row12_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 98 = [0, 3, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 98) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 98) (g32p_literalTraceValue 11 98)
      [1, -1, 1] [-11664, 0, 3888, 3888] = true := by
  rw [g32p_row12_traceCoefficients_098]
  decide +kernel

theorem g32p_row12_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 99 = [0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 99) (g32p_literalTraceValue 11 99)
      [1, -1, 1] [155520, 155520] = true := by
  rw [g32p_row12_traceCoefficients_099]
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

theorem g32p_row12_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 100 = [3, 0, 1] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 100) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 100) (g32p_literalTraceValue 11 100)
      [1, -1, 1] [] = true := by
  rw [g32p_row12_traceCoefficients_100]
  decide +kernel

theorem g32p_row12_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row12_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) 101) (g32p_literalTraceValue 11 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row12_traceCoefficients_101]
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

def g32p_row12_generatorIndex : Fin 8 → Fin 408 :=
  ![11, 62, 113, 164, 226, 227, 328, 329]

theorem g32p_row12_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup07_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 11 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 11 g32p_row12_supplierClass
    g32p_row12_supplierClass_isConj g32p_supplierGroup07_support g32p_row12_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row12_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup07_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row12_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 11 c false (g32p_row12_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 11 c true (g32p_row12_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 11 c false (g32p_row12_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 11 c true (g32p_row12_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 11 c false (g32p_row12_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 11 c false (g32p_row12_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 11 c true (g32p_row12_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 11 c true (g32p_row12_coinduced_zero c hc true) 3

theorem g32p_row12_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row12_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row12_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row12_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row12_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row12_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row12_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row12_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row12_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row12_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row12_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row12_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row12_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row12_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row12_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup07_support) :
    g32p_literalTraceValue (g32p_row12_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup07_support →
    g32p_literalTraceValue (g32p_row12_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row12_zeroTrace_block_00 r k
  · exact g32p_row12_zeroTrace_block_01 r k
  · exact g32p_row12_zeroTrace_block_02 r k
  · exact g32p_row12_zeroTrace_block_03 r k
  · exact g32p_row12_zeroTrace_block_04 r k
  · exact g32p_row12_zeroTrace_block_05 r k
  · exact g32p_row12_zeroTrace_block_06 r k

theorem g32p_row12_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup07_support) :
    (g32p_recordedInductionGenerators (g32p_row12_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row12_generatorIndex k) c) := by
  rw [g32p_row12_recordedGenerator_zero c hc k, g32p_row12_zeroTrace_arithmetic c k hc]
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

def g32p_row12_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [11664, 11664, 11664] else [3888, 3888, 3888])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [972, 972, 972] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [972, 972, 972] else (if i.val < 11 then [] else [1944, 1944, 1944])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [972, 972] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else [-1944, 0, 1944, 1944]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [11664, 11664, 3888, 3888] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [-6804, 972, 972, 972] else [972, 972])) else (if i.val < 36 then (if i.val < 35 then [] else [7776, 7776, 7776]) else (if i.val < 37 then [] else [-155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [0, 0, 972, 972] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [3888, 3888, 11664, 11664] else (if i.val < 46 then [972, 972, 972] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [-972])) else (if i.val < 55 then [] else (if i.val < 56 then [] else [0, 1944]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [0, 0, 972, 972])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [11664, 11664, 11664] else [972, 972, 972]))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [-972] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else [6804, 7776, 972, 972]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [1944, 1944, 1944])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [0, 972, 7776, 7776])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [3888, 3888, 3888] else [7776, 11664])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [1944, 1944, 1944, 1944] else (if i.val < 94 then [-3888, 0, 11664, 11664] else []))) else (if i.val < 98 then (if i.val < 96 then [-7776, 3888] else (if i.val < 97 then [] else [0, 0, 155520, 155520])) else (if i.val < 100 then (if i.val < 99 then [-11664, 0, 3888, 3888] else [155520, 155520]) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row12_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup07_support) :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) c) (g32p_literalTraceValue 11 c)
      [1, -1, 1] (g32p_row12_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row12_tracePolynomial_000
  · exact g32p_row12_tracePolynomial_001
  · exact g32p_row12_tracePolynomial_002
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_009
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_011
  · exact g32p_row12_tracePolynomial_012
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_014
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (18 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_032
  · exact g32p_row12_tracePolynomial_033
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_035
  · exact g32p_row12_tracePolynomial_036
  · exact g32p_row12_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_039
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_042
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_044
  · exact g32p_row12_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_053
  · exact g32p_row12_tracePolynomial_054
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_062
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_067
  · exact g32p_row12_tracePolynomial_068
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_070
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_075
  · exact g32p_row12_tracePolynomial_076
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_087
  · exact g32p_row12_tracePolynomial_088
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_092
  · exact g32p_row12_tracePolynomial_093
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row12_tracePolynomial_095
  · exact g32p_row12_tracePolynomial_096
  · exact g32p_row12_tracePolynomial_097
  · exact g32p_row12_tracePolynomial_098
  · exact g32p_row12_tracePolynomial_099
  · exact g32p_row12_tracePolynomial_100
  · exact g32p_row12_tracePolynomial_101

theorem g32p_row12_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 11 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 11 c) := by
  by_cases hc : c ∈ g32p_supplierGroup07_support
  · have hclass (j : Fin 486) :
        IsConj (g32p_literalRepresentative c) (g32p_row09_groupEquiv j : g32p_G) ↔
          g32p_row12_supplierClassifier j = c := by
      simpa only [g32p_row12_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row12_supplierClass_iff (g32p_row09_groupEquiv j) c
    have hχ (j : Fin 486) :
        (g32p_recordedSupplierCharacters 11 (g32p_row09_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row12_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 11 (show (g32p_recordedSuppliers 11).H from g32p_row09_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row12_characterValues (g32p_row09_groupEquiv.symm (g32p_row09_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 11).H (g32p_recordedSupplierCharacters 11)
      (g32p_literalRepresentative c) g32p_row09_groupEquiv g32p_row12_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row12_characterValues j)).val) c 6 486
      (g32p_literalCentralizer c) (g32p_literalTraceValue 11 c) [1, -1, 1]
      (g32p_row12_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row12_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 11)))
      (g32p_row12_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row12_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row12_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
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

theorem g32p_row12_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
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

theorem g32p_row12_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
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

theorem g32p_row12_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
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

theorem g32p_row12_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
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

theorem g32p_row12_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
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

theorem g32p_row12_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row12_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row12_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
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

theorem g32p_row12_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row12_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row12_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row12_variantArithmetic_00_0 r
  · exact g32p_row12_variantArithmetic_01_0 r
  · exact g32p_row12_variantArithmetic_02_0 r
  · exact g32p_row12_variantArithmetic_03_0 r
  · exact g32p_row12_variantArithmetic_04_0 r
  · exact g32p_row12_variantArithmetic_05_0 r
  · exact g32p_row12_variantArithmetic_06_0 r

theorem g32p_row12_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row12_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row12_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row12_variantArithmetic_00_1 r
  · exact g32p_row12_variantArithmetic_01_1 r
  · exact g32p_row12_variantArithmetic_02_1 r
  · exact g32p_row12_variantArithmetic_03_1 r
  · exact g32p_row12_variantArithmetic_04_1 r
  · exact g32p_row12_variantArithmetic_05_1 r
  · exact g32p_row12_variantArithmetic_06_1 r

theorem g32p_row12_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row12_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row12_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row12_variantArithmetic_00_2 r
  · exact g32p_row12_variantArithmetic_01_2 r
  · exact g32p_row12_variantArithmetic_02_2 r
  · exact g32p_row12_variantArithmetic_03_2 r
  · exact g32p_row12_variantArithmetic_04_2 r
  · exact g32p_row12_variantArithmetic_05_2 r
  · exact g32p_row12_variantArithmetic_06_2 r

theorem g32p_row12_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row12_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row12_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row12_variantArithmetic_00_3 r
  · exact g32p_row12_variantArithmetic_01_3 r
  · exact g32p_row12_variantArithmetic_02_3 r
  · exact g32p_row12_variantArithmetic_03_3 r
  · exact g32p_row12_variantArithmetic_04_3 r
  · exact g32p_row12_variantArithmetic_05_3 r
  · exact g32p_row12_variantArithmetic_06_3 r

theorem g32p_row12_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row12_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row12_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row12_variantArithmetic_00_4 r
  · exact g32p_row12_variantArithmetic_01_4 r
  · exact g32p_row12_variantArithmetic_02_4 r
  · exact g32p_row12_variantArithmetic_03_4 r
  · exact g32p_row12_variantArithmetic_04_4 r
  · exact g32p_row12_variantArithmetic_05_4 r
  · exact g32p_row12_variantArithmetic_06_4 r

theorem g32p_row12_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row12_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row12_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row12_variantArithmetic_00_5 r
  · exact g32p_row12_variantArithmetic_01_5 r
  · exact g32p_row12_variantArithmetic_02_5 r
  · exact g32p_row12_variantArithmetic_03_5 r
  · exact g32p_row12_variantArithmetic_04_5 r
  · exact g32p_row12_variantArithmetic_05_5 r
  · exact g32p_row12_variantArithmetic_06_5 r

theorem g32p_row12_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row12_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row12_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row12_variantArithmetic_00_6 r
  · exact g32p_row12_variantArithmetic_01_6 r
  · exact g32p_row12_variantArithmetic_02_6 r
  · exact g32p_row12_variantArithmetic_03_6 r
  · exact g32p_row12_variantArithmetic_04_6 r
  · exact g32p_row12_variantArithmetic_05_6 r
  · exact g32p_row12_variantArithmetic_06_6 r

theorem g32p_row12_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row12_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row12_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 11 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row12_variantArithmetic_00_7 r
  · exact g32p_row12_variantArithmetic_01_7 r
  · exact g32p_row12_variantArithmetic_02_7 r
  · exact g32p_row12_variantArithmetic_03_7 r
  · exact g32p_row12_variantArithmetic_04_7 r
  · exact g32p_row12_variantArithmetic_05_7 r
  · exact g32p_row12_variantArithmetic_06_7 r

theorem g32p_row12_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row12_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row12_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 11 c _ (g32p_row12_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row12_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 11 c _ (g32p_row12_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row12_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 11 c _ (g32p_row12_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row12_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 11 c _ (g32p_row12_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row12_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 11 c _ (g32p_row12_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row12_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 11 c _ (g32p_row12_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row12_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 11 c _ (g32p_row12_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row12_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 11 c _ (g32p_row12_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row12_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_archiveNodes : Fin 134 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 67 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]] else ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]) else (if i.val < 3 then ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]] else ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]])) else (if i.val < 6 then (if i.val < 5 then ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]] else ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]) else (if i.val < 7 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]] else ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]] else ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]) else (if i.val < 11 then ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]] else ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])) else (if i.val < 14 then (if i.val < 13 then ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]] else ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]) else (if i.val < 15 then ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]] else ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]] else ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]) else (if i.val < 19 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]] else ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]])) else (if i.val < 22 then (if i.val < 21 then ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]] else ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]) else (if i.val < 23 then ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]] else ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]] else ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]) else (if i.val < 27 then ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]] else ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]])) else (if i.val < 30 then (if i.val < 29 then ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]] else ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]) else (if i.val < 31 then ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]] else (if i.val < 32 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]] else ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]])))))) else (if i.val < 50 then (if i.val < 41 then (if i.val < 37 then (if i.val < 35 then (if i.val < 34 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]] else ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]) else (if i.val < 36 then ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]] else ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]])) else (if i.val < 39 then (if i.val < 38 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]] else ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]) else (if i.val < 40 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]] else ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]))) else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]] else ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]) else (if i.val < 44 then ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]] else ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]])) else (if i.val < 47 then (if i.val < 46 then ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]] else ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]) else (if i.val < 48 then ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]] else (if i.val < 49 then ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]] else ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]))))) else (if i.val < 58 then (if i.val < 54 then (if i.val < 52 then (if i.val < 51 then ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]] else ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]) else (if i.val < 53 then ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]] else ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]])) else (if i.val < 56 then (if i.val < 55 then ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]] else ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]) else (if i.val < 57 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]] else ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))) else (if i.val < 62 then (if i.val < 60 then (if i.val < 59 then ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]] else ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]) else (if i.val < 61 then ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]] else ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])) else (if i.val < 64 then (if i.val < 63 then ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]] else ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]) else (if i.val < 65 then ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]] else (if i.val < 66 then ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]] else ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]))))))) else (if i.val < 100 then (if i.val < 83 then (if i.val < 75 then (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]] else ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]) else (if i.val < 70 then ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]] else ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]])) else (if i.val < 73 then (if i.val < 72 then ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]] else ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]) else (if i.val < 74 then ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]] else ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]))) else (if i.val < 79 then (if i.val < 77 then (if i.val < 76 then ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]] else ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]) else (if i.val < 78 then ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]] else ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]])) else (if i.val < 81 then (if i.val < 80 then ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]] else ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]) else (if i.val < 82 then ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]] else ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]])))) else (if i.val < 91 then (if i.val < 87 then (if i.val < 85 then (if i.val < 84 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]] else ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]) else (if i.val < 86 then ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]] else ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]])) else (if i.val < 89 then (if i.val < 88 then ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]] else ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]) else (if i.val < 90 then ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]] else ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]))) else (if i.val < 95 then (if i.val < 93 then (if i.val < 92 then ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]] else ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]) else (if i.val < 94 then ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]] else ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])) else (if i.val < 97 then (if i.val < 96 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]] else ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]) else (if i.val < 98 then ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]] else (if i.val < 99 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]] else ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]])))))) else (if i.val < 117 then (if i.val < 108 then (if i.val < 104 then (if i.val < 102 then (if i.val < 101 then ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]] else ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]) else (if i.val < 103 then ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]] else ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]])) else (if i.val < 106 then (if i.val < 105 then ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]] else ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]) else (if i.val < 107 then ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]] else ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]))) else (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]] else ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]) else (if i.val < 111 then ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]] else ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]])) else (if i.val < 114 then (if i.val < 113 then ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]] else ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]) else (if i.val < 115 then ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]] else (if i.val < 116 then ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]] else ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]))))) else (if i.val < 125 then (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]] else ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]) else (if i.val < 120 then ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]] else ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]])) else (if i.val < 123 then (if i.val < 122 then ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]] else ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]) else (if i.val < 124 then ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]] else ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]))) else (if i.val < 129 then (if i.val < 127 then (if i.val < 126 then ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]] else ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]) else (if i.val < 128 then ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]] else ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]])) else (if i.val < 131 then (if i.val < 130 then ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]] else ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]) else (if i.val < 132 then ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]] else (if i.val < 133 then ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]] else ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]))))))))

def g32p_row13_archiveParent : Fin 134 → Fin 134 :=
  fun i => (if i.val < 67 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 1) else (if i.val < 3 then 5 else 3)) else (if i.val < 6 then (if i.val < 5 then 3 else 1) else (if i.val < 7 then 2 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 10) else (if i.val < 11 then 1 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 17) else (if i.val < 15 then 16 else 3)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 11 else 6) else (if i.val < 19 then 4 else 19)) else (if i.val < 22 then (if i.val < 21 then 22 else 21) else (if i.val < 23 then 7 else 8))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 70 else 35) else (if i.val < 27 then 58 else 59)) else (if i.val < 30 then (if i.val < 29 then 36 else 18) else (if i.val < 31 then 21 else (if i.val < 32 then 32 else 23)))))) else (if i.val < 50 then (if i.val < 41 then (if i.val < 37 then (if i.val < 35 then (if i.val < 34 then 16 else 7) else (if i.val < 36 then 37 else 30)) else (if i.val < 39 then (if i.val < 38 then 15 else 26) else (if i.val < 40 then 12 else 14))) else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then 39 else 62) else (if i.val < 44 then 43 else 44)) else (if i.val < 47 then (if i.val < 46 then 49 else 63) else (if i.val < 48 then 40 else (if i.val < 49 then 27 else 29))))) else (if i.val < 58 then (if i.val < 54 then (if i.val < 52 then (if i.val < 51 then 50 else 51) else (if i.val < 53 then 52 else 67)) else (if i.val < 56 then (if i.val < 55 then 65 else 31) else (if i.val < 57 then 78 else 102))) else (if i.val < 62 then (if i.val < 60 then (if i.val < 59 then 41 else 19) else (if i.val < 61 then 75 else 69)) else (if i.val < 64 then (if i.val < 63 then 33 else 45) else (if i.val < 65 then 71 else (if i.val < 66 then 25 else 80))))))) else (if i.val < 100 then (if i.val < 83 then (if i.val < 75 then (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then 56 else 64) else (if i.val < 70 then 59 else 38)) else (if i.val < 73 then (if i.val < 72 then 95 else 86) else (if i.val < 74 then 81 else 83))) else (if i.val < 79 then (if i.val < 77 then (if i.val < 76 then 44 else 72) else (if i.val < 78 then 73 else 55)) else (if i.val < 81 then (if i.val < 80 then 74 else 93) else (if i.val < 82 then 82 else 79)))) else (if i.val < 91 then (if i.val < 87 then (if i.val < 85 then (if i.val < 84 then 48 else 51) else (if i.val < 86 then 52 else 34)) else (if i.val < 89 then (if i.val < 88 then 117 else 47) else (if i.val < 90 then 92 else 42))) else (if i.val < 95 then (if i.val < 93 then (if i.val < 92 then 115 else 96) else (if i.val < 94 then 89 else 94)) else (if i.val < 97 then (if i.val < 96 then 43 else 61) else (if i.val < 98 then 68 else (if i.val < 99 then 75 else 130)))))) else (if i.val < 117 then (if i.val < 108 then (if i.val < 104 then (if i.val < 102 then (if i.val < 101 then 100 else 100) else (if i.val < 103 then 88 else 118)) else (if i.val < 106 then (if i.val < 105 then 94 else 60) else (if i.val < 107 then 132 else 128))) else (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 104 else 122) else (if i.val < 111 then 124 else 98)) else (if i.val < 114 then (if i.val < 113 then 110 else 120) else (if i.val < 115 then 119 else (if i.val < 116 then 85 else 111))))) else (if i.val < 125 then (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 112 else 90) else (if i.val < 120 then 113 else 94)) else (if i.val < 123 then (if i.val < 122 then 91 else 114) else (if i.val < 124 then 76 else 105))) else (if i.val < 129 then (if i.val < 127 then (if i.val < 126 then 107 else 101) else (if i.val < 128 then 50 else 108)) else (if i.val < 131 then (if i.val < 130 then 127 else 131) else (if i.val < 132 then 129 else (if i.val < 133 then 116 else 133))))))))

def g32p_row13_archiveDepth : Fin 134 → ℕ :=
  fun i => (if i.val < 67 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 2 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 3 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 2) else (if i.val < 11 then 1 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 5) else (if i.val < 15 then 2 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 1 else 4) else (if i.val < 19 then 2 else 0)) else (if i.val < 22 then (if i.val < 21 then 2 else 0) else (if i.val < 23 then 1 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 7 else 4) else (if i.val < 27 then 4 else 2)) else (if i.val < 30 then (if i.val < 29 then 3 else 3) else (if i.val < 31 then 1 else (if i.val < 32 then 3 else 2)))))) else (if i.val < 50 then (if i.val < 41 then (if i.val < 37 then (if i.val < 35 then (if i.val < 34 then 2 else 1) else (if i.val < 36 then 3 else 2)) else (if i.val < 39 then (if i.val < 38 then 2 else 5) else (if i.val < 40 then 1 else 3))) else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then 2 else 4) else (if i.val < 44 then 0 else 0)) else (if i.val < 47 then (if i.val < 46 then 5 else 7) else (if i.val < 48 then 4 else (if i.val < 49 then 3 else 4))))) else (if i.val < 58 then (if i.val < 54 then (if i.val < 52 then (if i.val < 51 then 0 else 0) else (if i.val < 53 then 0 else 8)) else (if i.val < 56 then (if i.val < 55 then 6 else 4) else (if i.val < 57 then 6 else 7))) else (if i.val < 62 then (if i.val < 60 then (if i.val < 59 then 3 else 1) else (if i.val < 61 then 2 else 3)) else (if i.val < 64 then (if i.val < 63 then 3 else 6) else (if i.val < 65 then 3 else (if i.val < 66 then 5 else 9))))))) else (if i.val < 100 then (if i.val < 83 then (if i.val < 75 then (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then 7 else 4) else (if i.val < 70 then 2 else 6)) else (if i.val < 73 then (if i.val < 72 then 2 else 3) else (if i.val < 74 then 9 else 5))) else (if i.val < 79 then (if i.val < 77 then (if i.val < 76 then 1 else 4) else (if i.val < 78 then 10 else 5)) else (if i.val < 81 then (if i.val < 80 then 6 else 8) else (if i.val < 82 then 8 else 7)))) else (if i.val < 91 then (if i.val < 87 then (if i.val < 85 then (if i.val < 84 then 4 else 1) else (if i.val < 86 then 1 else 2)) else (if i.val < 89 then (if i.val < 88 then 8 else 5) else (if i.val < 90 then 6 else 5))) else (if i.val < 95 then (if i.val < 93 then (if i.val < 92 then 3 else 5) else (if i.val < 94 then 7 else 0)) else (if i.val < 97 then (if i.val < 96 then 1 else 4) else (if i.val < 98 then 5 else (if i.val < 99 then 2 else 5)))))) else (if i.val < 117 then (if i.val < 108 then (if i.val < 104 then (if i.val < 102 then (if i.val < 101 then 0 else 1) else (if i.val < 103 then 6 else 7)) else (if i.val < 106 then (if i.val < 105 then 1 else 3) else (if i.val < 107 then 6 else 4))) else (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 2 else 6) else (if i.val < 111 then 5 else 3)) else (if i.val < 114 then (if i.val < 113 then 6 else 2) else (if i.val < 115 then 4 else (if i.val < 116 then 2 else 4))))) else (if i.val < 125 then (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 7 else 6) else (if i.val < 120 then 3 else 1)) else (if i.val < 123 then (if i.val < 122 then 4 else 5) else (if i.val < 124 then 5 else 4))) else (if i.val < 129 then (if i.val < 127 then (if i.val < 126 then 5 else 2) else (if i.val < 128 then 1 else 3)) else (if i.val < 131 then (if i.val < 130 then 2 else 4) else (if i.val < 132 then 3 else (if i.val < 133 then 5 else 0))))))))

def g32p_row13_archiveClass : Fin 134 → Fin 102 :=
  fun i => (if i.val < 67 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 5) else (if i.val < 3 then 5 else 7)) else (if i.val < 6 then (if i.val < 5 then 7 else 5) else (if i.val < 7 then 5 else 18))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 19 else 5) else (if i.val < 11 then 5 else 20)) else (if i.val < 14 then (if i.val < 13 then 23 else 5) else (if i.val < 15 then 20 else 7)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 20 else 5) else (if i.val < 19 then 7 else 41)) else (if i.val < 22 then (if i.val < 21 then 18 else 44) else (if i.val < 23 then 18 else 19))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 23 else 7) else (if i.val < 27 then 23 else 41)) else (if i.val < 30 then (if i.val < 29 then 44 else 7) else (if i.val < 31 then 44 else (if i.val < 32 then 19 else 19)))))) else (if i.val < 50 then (if i.val < 41 then (if i.val < 37 then (if i.val < 35 then (if i.val < 34 then 20 else 18) else (if i.val < 36 then 7 else 44)) else (if i.val < 39 then (if i.val < 38 then 7 else 23) else (if i.val < 40 then 23 else 20))) else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then 23 else 20) else (if i.val < 44 then 67 else 72)) else (if i.val < 47 then (if i.val < 46 then 7 else 7) else (if i.val < 48 then 20 else (if i.val < 49 then 41 else 7))))) else (if i.val < 58 then (if i.val < 54 then (if i.val < 52 then (if i.val < 51 then 76 else 77) else (if i.val < 53 then 79 else 19)) else (if i.val < 56 then (if i.val < 55 then 7 else 19) else (if i.val < 57 then 19 else 20))) else (if i.val < 62 then (if i.val < 60 then (if i.val < 59 then 23 else 41) else (if i.val < 61 then 72 else 41)) else (if i.val < 64 then (if i.val < 63 then 20 else 7) else (if i.val < 65 then 67 else (if i.val < 66 then 7 else 41))))))) else (if i.val < 100 then (if i.val < 83 then (if i.val < 75 then (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then 19 else 67) else (if i.val < 70 then 41 else 23)) else (if i.val < 73 then (if i.val < 72 then 67 else 18) else (if i.val < 74 then 41 else 41))) else (if i.val < 79 then (if i.val < 77 then (if i.val < 76 then 72 else 18) else (if i.val < 78 then 41 else 19)) else (if i.val < 81 then (if i.val < 80 then 41 else 41) else (if i.val < 82 then 41 else 41)))) else (if i.val < 91 then (if i.val < 87 then (if i.val < 85 then (if i.val < 84 then 41 else 77) else (if i.val < 86 then 79 else 18)) else (if i.val < 89 then (if i.val < 88 then 72 else 20) else (if i.val < 90 then 41 else 20))) else (if i.val < 95 then (if i.val < 93 then (if i.val < 92 then 79 else 41) else (if i.val < 94 then 41 else 94)) else (if i.val < 97 then (if i.val < 96 then 67 else 41) else (if i.val < 98 then 67 else (if i.val < 99 then 72 else 76)))))) else (if i.val < 117 then (if i.val < 108 then (if i.val < 104 then (if i.val < 102 then (if i.val < 101 then 95 else 95) else (if i.val < 103 then 20 else 20)) else (if i.val < 106 then (if i.val < 105 then 94 else 72) else (if i.val < 107 then 72 else 94))) else (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 94 else 94) else (if i.val < 111 then 72 else 72)) else (if i.val < 114 then (if i.val < 113 then 72 else 94) else (if i.val < 115 then 94 else (if i.val < 116 then 79 else 72))))) else (if i.val < 125 then (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 72 else 20) else (if i.val < 120 then 94 else 94)) else (if i.val < 123 then (if i.val < 122 then 79 else 94) else (if i.val < 124 then 18 else 72))) else (if i.val < 129 then (if i.val < 127 then (if i.val < 126 then 94 else 95) else (if i.val < 128 then 76 else 94)) else (if i.val < 131 then (if i.val < 130 then 76 else 76) else (if i.val < 132 then 76 else (if i.val < 133 then 72 else 99))))))))

def g32p_row13_archiveLabel : Fin 134 → Fin 4 :=
  fun i => (if i.val < 67 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 0) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 2 else 0) else (if i.val < 7 then 1 else 0))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 0 else 1) else (if i.val < 11 then 2 else 0)) else (if i.val < 14 then (if i.val < 13 then 0 else 1) else (if i.val < 15 then 1 else 1)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 0 else 2) else (if i.val < 19 then 3 else 0)) else (if i.val < 22 then (if i.val < 21 then 1 else 0) else (if i.val < 23 then 2 else 2))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 3 else 1) else (if i.val < 27 then 1 else 1)) else (if i.val < 30 then (if i.val < 29 then 0 else 0) else (if i.val < 31 then 1 else (if i.val < 32 then 0 else 1)))))) else (if i.val < 50 then (if i.val < 41 then (if i.val < 37 then (if i.val < 35 then (if i.val < 34 then 3 else 3) else (if i.val < 36 then 0 else 3)) else (if i.val < 39 then (if i.val < 38 then 3 else 1) else (if i.val < 40 then 3 else 3))) else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then 3 else 2) else (if i.val < 44 then 0 else 0)) else (if i.val < 47 then (if i.val < 46 then 2 else 0) else (if i.val < 48 then 2 else (if i.val < 49 then 0 else 2))))) else (if i.val < 58 then (if i.val < 54 then (if i.val < 52 then (if i.val < 51 then 0 else 0) else (if i.val < 53 then 0 else 0)) else (if i.val < 56 then (if i.val < 55 then 3 else 3) else (if i.val < 57 then 2 else 1))) else (if i.val < 62 then (if i.val < 60 then (if i.val < 59 then 2 else 1) else (if i.val < 61 then 0 else 0)) else (if i.val < 64 then (if i.val < 63 then 0 else 1) else (if i.val < 65 then 1 else (if i.val < 66 then 2 else 3))))))) else (if i.val < 100 then (if i.val < 83 then (if i.val < 75 then (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then 3 else 2) else (if i.val < 70 then 0 else 0)) else (if i.val < 73 then (if i.val < 72 then 0 else 2) else (if i.val < 74 then 2 else 2))) else (if i.val < 79 then (if i.val < 77 then (if i.val < 76 then 1 else 1) else (if i.val < 78 then 2 else 2)) else (if i.val < 81 then (if i.val < 80 then 1 else 3) else (if i.val < 82 then 3 else 0)))) else (if i.val < 91 then (if i.val < 87 then (if i.val < 85 then (if i.val < 84 then 3 else 0) else (if i.val < 86 then 0 else 2)) else (if i.val < 89 then (if i.val < 88 then 3 else 2) else (if i.val < 90 then 1 else 2))) else (if i.val < 95 then (if i.val < 93 then (if i.val < 92 then 1 else 2) else (if i.val < 94 then 1 else 0)) else (if i.val < 97 then (if i.val < 96 then 3 else 1) else (if i.val < 98 then 3 else (if i.val < 99 then 3 else 3)))))) else (if i.val < 117 then (if i.val < 108 then (if i.val < 104 then (if i.val < 102 then (if i.val < 101 then 0 else 1) else (if i.val < 103 then 1 else 0)) else (if i.val < 106 then (if i.val < 105 then 2 else 3) else (if i.val < 107 then 2 else 2))) else (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 2 else 2) else (if i.val < 111 then 2 else 0)) else (if i.val < 114 then (if i.val < 113 then 1 else 0) else (if i.val < 115 then 3 else (if i.val < 116 then 1 else 0))))) else (if i.val < 125 then (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 0 else 1) else (if i.val < 120 then 2 else 0)) else (if i.val < 123 then (if i.val < 122 then 3 else 3) else (if i.val < 124 then 3 else 2))) else (if i.val < 129 then (if i.val < 127 then (if i.val < 126 then 1 else 0) else (if i.val < 128 then 3 else 3)) else (if i.val < 131 then (if i.val < 130 then 0 else 2) else (if i.val < 132 then 1 else (if i.val < 133 then 3 else 0))))))))

def g32p_row13_archiveSourceIndex : Fin 24 → Fin 134 :=
  ![0, 9, 97, 133, 20, 54, 109, 99, 126, 13, 24, 123, 103, 106, 28, 46, 125, 53, 121, 77, 57, 87, 84, 66]

def g32p_row13_supplierClassifier : Fin 24 → Fin 102 :=
  ![0, 5, 67, 99, 18, 7, 94, 76, 95, 5, 23, 18, 20, 72, 44, 7, 94, 19, 79, 41, 20, 72, 77, 41]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_archive_root_block_00 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 0 r) = 0 →
      g32p_row13_archiveNodes (g32p_finBlockIndex 134 0 r) = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass (g32p_finBlockIndex 134 0 r)) := by
  decide +kernel

theorem g32p_row13_archive_depth_block_00 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 0 r) ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent (g32p_finBlockIndex 134 0 r)) < g32p_row13_archiveDepth (g32p_finBlockIndex 134 0 r) := by
  decide +kernel

theorem g32p_row13_archive_class_block_00 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 0 r) ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent (g32p_finBlockIndex 134 0 r)) = g32p_row13_archiveClass (g32p_finBlockIndex 134 0 r) := by
  decide +kernel

theorem g32p_row13_archive_step_block_00 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 0 r) ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes (g32p_finBlockIndex 134 0 r))
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 0 r))) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 0 r)))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent (g32p_finBlockIndex 134 0 r))) := by
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

theorem g32p_row13_archive_root_block_01 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 1 r) = 0 →
      g32p_row13_archiveNodes (g32p_finBlockIndex 134 1 r) = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass (g32p_finBlockIndex 134 1 r)) := by
  decide +kernel

theorem g32p_row13_archive_depth_block_01 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 1 r) ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent (g32p_finBlockIndex 134 1 r)) < g32p_row13_archiveDepth (g32p_finBlockIndex 134 1 r) := by
  decide +kernel

theorem g32p_row13_archive_class_block_01 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 1 r) ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent (g32p_finBlockIndex 134 1 r)) = g32p_row13_archiveClass (g32p_finBlockIndex 134 1 r) := by
  decide +kernel

theorem g32p_row13_archive_step_block_01 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 1 r) ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes (g32p_finBlockIndex 134 1 r))
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 1 r))) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 1 r)))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent (g32p_finBlockIndex 134 1 r))) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
