import HodgeLean.Foundations.Program.G32PropFourSixPacked0433
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixPacked0414
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row46_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 69 = [18, 0, 0, 12] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 69) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 69) (g32p_literalTraceValue 45 69)
      [1, -1, 1] [3456, 3456] = true := by
  rw [g32p_row46_traceCoefficients_069]
  decide +kernel

theorem g32p_row46_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 71 = [0, 0, 0, 12] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 71) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 71) (g32p_literalTraceValue 45 71)
      [1, -1, 1] [1296, 1296] = true := by
  rw [g32p_row46_traceCoefficients_071]
  decide +kernel

theorem g32p_row46_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 75 = [4] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 75) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 75) (g32p_literalTraceValue 45 75)
      [1, -1, 1] [] = true := by
  rw [g32p_row46_traceCoefficients_075]
  decide +kernel

theorem g32p_row46_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 78 = [4] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 78) (g32p_literalTraceValue 45 78)
      [1, -1, 1] [] = true := by
  rw [g32p_row46_traceCoefficients_078]
  decide +kernel

theorem g32p_row46_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 82 = [0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 82) (g32p_literalTraceValue 45 82)
      [1, -1, 1] [0, 0, 20736, 20736] = true := by
  rw [g32p_row46_traceCoefficients_082]
  decide +kernel

theorem g32p_row46_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 84 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 84) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 84) (g32p_literalTraceValue 45 84)
      [1, -1, 1] [] = true := by
  rw [g32p_row46_traceCoefficients_084]
  decide +kernel

theorem g32p_row46_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 86 = [0, 0, 0, 0, 0, 12] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 86) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 86) (g32p_literalTraceValue 45 86)
      [1, -1, 1] [0, 0, 1296, 1296] = true := by
  rw [g32p_row46_traceCoefficients_086]
  decide +kernel

theorem g32p_row46_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 92 = [0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 92) (g32p_literalTraceValue 45 92)
      [1, -1, 1] [2592, 2592, 2592] = true := by
  rw [g32p_row46_traceCoefficients_092]
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

theorem g32p_row46_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 96 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 96) (g32p_literalTraceValue 45 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row46_traceCoefficients_096]
  decide +kernel

theorem g32p_row46_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 97 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 97) (g32p_literalTraceValue 45 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row46_traceCoefficients_097]
  decide +kernel

theorem g32p_row46_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 99 = [1] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 99) (g32p_literalTraceValue 45 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row46_traceCoefficients_099]
  decide +kernel

theorem g32p_row46_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row46_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) 101) (g32p_literalTraceValue 45 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row46_traceCoefficients_101]
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

def g32p_row46_generatorIndex : Fin 8 → Fin 408 :=
  ![45, 96, 147, 198, 294, 295, 396, 397]

theorem g32p_row46_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup31_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 45 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 45 g32p_row46_supplierClass
    g32p_row46_supplierClass_isConj g32p_supplierGroup31_support g32p_row46_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row46_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup31_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row46_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 45 c false (g32p_row46_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 45 c true (g32p_row46_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 45 c false (g32p_row46_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 45 c true (g32p_row46_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 45 c false (g32p_row46_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 45 c false (g32p_row46_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 45 c true (g32p_row46_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 45 c true (g32p_row46_coinduced_zero c hc true) 3

theorem g32p_row46_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup31_support →
      g32p_literalTraceValue (g32p_row46_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row46_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup31_support →
      g32p_literalTraceValue (g32p_row46_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row46_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup31_support →
      g32p_literalTraceValue (g32p_row46_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row46_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup31_support →
      g32p_literalTraceValue (g32p_row46_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row46_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup31_support →
      g32p_literalTraceValue (g32p_row46_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row46_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup31_support →
      g32p_literalTraceValue (g32p_row46_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row46_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup31_support →
      g32p_literalTraceValue (g32p_row46_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row46_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup31_support) :
    g32p_literalTraceValue (g32p_row46_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup31_support →
    g32p_literalTraceValue (g32p_row46_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row46_zeroTrace_block_00 r k
  · exact g32p_row46_zeroTrace_block_01 r k
  · exact g32p_row46_zeroTrace_block_02 r k
  · exact g32p_row46_zeroTrace_block_03 r k
  · exact g32p_row46_zeroTrace_block_04 r k
  · exact g32p_row46_zeroTrace_block_05 r k
  · exact g32p_row46_zeroTrace_block_06 r k

theorem g32p_row46_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup31_support) :
    (g32p_recordedInductionGenerators (g32p_row46_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row46_generatorIndex k) c) := by
  rw [g32p_row46_recordedGenerator_zero c hc k, g32p_row46_zeroTrace_arithmetic c k hc]
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

def g32p_row46_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [2592, 2592, 2592] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [0, 0, 1296, 1296] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 3456, 3456] else [])) else (if i.val < 16 then [-1296] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [20736, 20736] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [864, 864] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else [-864]))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [1296, 1296, 1296] else [])) else (if i.val < 36 then (if i.val < 35 then [1728, 5184, 5184] else [1296, 1296, 1296]) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [1296, 1296])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [0, 0, 864, 864])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [864, 864, 864] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [-20736])) else (if i.val < 67 then [-1296] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [3456, 3456] else (if i.val < 71 then [] else [1296, 1296])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [0, 0, 20736, 20736] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else [0, 0, 1296, 1296]) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [2592, 2592, 2592] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row46_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup31_support) :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) c) (g32p_literalTraceValue 45 c)
      [1, -1, 1] (g32p_row46_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row46_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_010
  · exact g32p_row46_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_021
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_030
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_034
  · exact g32p_row46_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_037
  · exact g32p_row46_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_040
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_045
  · exact g32p_row46_tracePolynomial_046
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_049
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_056
  · exact g32p_row46_tracePolynomial_057
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_065
  · exact g32p_row46_tracePolynomial_066
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_071
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_075
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_082
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_086
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_092
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_096
  · exact g32p_row46_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup31_support) hc)
  · exact g32p_row46_tracePolynomial_101

theorem g32p_row46_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 45 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 45 c) := by
  by_cases hc : c ∈ g32p_supplierGroup31_support
  · have hclass (j : Fin 432) :
        IsConj (g32p_literalRepresentative c) (g32p_row46_groupEquiv j : g32p_G) ↔
          g32p_row46_supplierClassifier j = c := by
      simpa only [g32p_row46_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row46_supplierClass_iff (g32p_row46_groupEquiv j) c
    have hχ (j : Fin 432) :
        (g32p_recordedSupplierCharacters 45 (g32p_row46_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row46_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 45 (show (g32p_recordedSuppliers 45).H from g32p_row46_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row46_characterValues (g32p_row46_groupEquiv.symm (g32p_row46_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 45).H (g32p_recordedSupplierCharacters 45)
      (g32p_literalRepresentative c) g32p_row46_groupEquiv g32p_row46_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row46_characterValues j)).val) c 6 432
      (g32p_literalCentralizer c) (g32p_literalTraceValue 45 c) [1, -1, 1]
      (g32p_row46_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row46_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 45)))
      (g32p_row46_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row46_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row46_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
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

theorem g32p_row46_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
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

theorem g32p_row46_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
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

theorem g32p_row46_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
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

theorem g32p_row46_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
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

theorem g32p_row46_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
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

theorem g32p_row46_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row46_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row46_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
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

theorem g32p_row46_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row46_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row46_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row46_variantArithmetic_00_0 r
  · exact g32p_row46_variantArithmetic_01_0 r
  · exact g32p_row46_variantArithmetic_02_0 r
  · exact g32p_row46_variantArithmetic_03_0 r
  · exact g32p_row46_variantArithmetic_04_0 r
  · exact g32p_row46_variantArithmetic_05_0 r
  · exact g32p_row46_variantArithmetic_06_0 r

theorem g32p_row46_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row46_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row46_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row46_variantArithmetic_00_1 r
  · exact g32p_row46_variantArithmetic_01_1 r
  · exact g32p_row46_variantArithmetic_02_1 r
  · exact g32p_row46_variantArithmetic_03_1 r
  · exact g32p_row46_variantArithmetic_04_1 r
  · exact g32p_row46_variantArithmetic_05_1 r
  · exact g32p_row46_variantArithmetic_06_1 r

theorem g32p_row46_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row46_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row46_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row46_variantArithmetic_00_2 r
  · exact g32p_row46_variantArithmetic_01_2 r
  · exact g32p_row46_variantArithmetic_02_2 r
  · exact g32p_row46_variantArithmetic_03_2 r
  · exact g32p_row46_variantArithmetic_04_2 r
  · exact g32p_row46_variantArithmetic_05_2 r
  · exact g32p_row46_variantArithmetic_06_2 r

theorem g32p_row46_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row46_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row46_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row46_variantArithmetic_00_3 r
  · exact g32p_row46_variantArithmetic_01_3 r
  · exact g32p_row46_variantArithmetic_02_3 r
  · exact g32p_row46_variantArithmetic_03_3 r
  · exact g32p_row46_variantArithmetic_04_3 r
  · exact g32p_row46_variantArithmetic_05_3 r
  · exact g32p_row46_variantArithmetic_06_3 r

theorem g32p_row46_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row46_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row46_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row46_variantArithmetic_00_4 r
  · exact g32p_row46_variantArithmetic_01_4 r
  · exact g32p_row46_variantArithmetic_02_4 r
  · exact g32p_row46_variantArithmetic_03_4 r
  · exact g32p_row46_variantArithmetic_04_4 r
  · exact g32p_row46_variantArithmetic_05_4 r
  · exact g32p_row46_variantArithmetic_06_4 r

theorem g32p_row46_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row46_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row46_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row46_variantArithmetic_00_5 r
  · exact g32p_row46_variantArithmetic_01_5 r
  · exact g32p_row46_variantArithmetic_02_5 r
  · exact g32p_row46_variantArithmetic_03_5 r
  · exact g32p_row46_variantArithmetic_04_5 r
  · exact g32p_row46_variantArithmetic_05_5 r
  · exact g32p_row46_variantArithmetic_06_5 r

theorem g32p_row46_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row46_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row46_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row46_variantArithmetic_00_6 r
  · exact g32p_row46_variantArithmetic_01_6 r
  · exact g32p_row46_variantArithmetic_02_6 r
  · exact g32p_row46_variantArithmetic_03_6 r
  · exact g32p_row46_variantArithmetic_04_6 r
  · exact g32p_row46_variantArithmetic_05_6 r
  · exact g32p_row46_variantArithmetic_06_6 r

theorem g32p_row46_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row46_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row46_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 45 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row46_variantArithmetic_00_7 r
  · exact g32p_row46_variantArithmetic_01_7 r
  · exact g32p_row46_variantArithmetic_02_7 r
  · exact g32p_row46_variantArithmetic_03_7 r
  · exact g32p_row46_variantArithmetic_04_7 r
  · exact g32p_row46_variantArithmetic_05_7 r
  · exact g32p_row46_variantArithmetic_06_7 r

theorem g32p_row46_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row46_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row46_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 45 c _ (g32p_row46_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row46_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 45 c _ (g32p_row46_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row46_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 45 c _ (g32p_row46_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row46_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 45 c _ (g32p_row46_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row46_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 45 c _ (g32p_row46_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row46_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 45 c _ (g32p_row46_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row46_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 45 c _ (g32p_row46_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row46_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 45 c _ (g32p_row46_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row46_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row47_supplierClassifier : Fin 432 → Fin 102 := g32p_supplierGroup24_classify

theorem g32p_row47_groupEquiv_isConj (i : Fin 432) :
    IsConj (g32p_row33_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row47_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup24_source i).1 (g32p_supplierGroup24_source i).2
  rw [g32p_supplierGroup24_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row33_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup24_matrix i)

def g32p_row47_supplierClass (h : (g32p_recordedSuppliers 46).H) : Fin 102 :=
  g32p_row47_supplierClassifier (g32p_row33_groupEquiv.symm h)

theorem g32p_row47_supplierClass_isConj (h : (g32p_recordedSuppliers 46).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row47_supplierClass h)) := by
  have he : (g32p_row33_groupEquiv (g32p_row33_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 46).H => (a : g32p_G))
      (g32p_row33_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row47_supplierClassifier (g32p_row33_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row47_groupEquiv_isConj (g32p_row33_groupEquiv.symm h)

theorem g32p_row47_supplierClass_iff (h : (g32p_recordedSuppliers 46).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row47_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row47_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row47_supplierClass_isConj h).symm

theorem g32p_row47_supplierClass_mem_support (h : (g32p_recordedSuppliers 46).H) :
    g32p_row47_supplierClass h ∈ g32p_supplierGroup24_support :=
  g32p_supplierGroup24_support_mem (g32p_row33_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row47_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 0) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 0) (g32p_literalTraceValue 46 0)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_000]
  decide +kernel

theorem g32p_row47_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 1 = [1, 0, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 1) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 1) (g32p_literalTraceValue 46 1)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row47_traceCoefficients_001]
  decide +kernel

theorem g32p_row47_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 2 = [1, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 2) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 2) (g32p_literalTraceValue 46 2)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_002]
  decide +kernel

theorem g32p_row47_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 3 = [1, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 3) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 3) (g32p_literalTraceValue 46 3)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_003]
  decide +kernel

theorem g32p_row47_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 4 = [0, 0, 8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 4) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 4) (g32p_literalTraceValue 46 4)
      [1, 1, 1] [5184] = true := by
  rw [g32p_row47_traceCoefficients_004]
  decide +kernel

theorem g32p_row47_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 5 = [6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 5) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 5) (g32p_literalTraceValue 46 5)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_005]
  decide +kernel

theorem g32p_row47_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 6 = [0, 4, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 6) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 6) (g32p_literalTraceValue 46 6)
      [1, 1, 1] [1296] = true := by
  rw [g32p_row47_traceCoefficients_006]
  decide +kernel

theorem g32p_row47_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 7 = [0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 7) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 7) (g32p_literalTraceValue 46 7)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_007]
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

theorem g32p_row47_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 8 = [1, 0, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 8) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 8) (g32p_literalTraceValue 46 8)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row47_traceCoefficients_008]
  decide +kernel

theorem g32p_row47_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 10 = [4, 0, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 10) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 10) (g32p_literalTraceValue 46 10)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_010]
  decide +kernel

theorem g32p_row47_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 11 = [0, 8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 11) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 11) (g32p_literalTraceValue 46 11)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_011]
  decide +kernel

theorem g32p_row47_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 15 = [4, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 15) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 15) (g32p_literalTraceValue 46 15)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_015]
  decide +kernel

theorem g32p_row47_traceCoefficients_017 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 17 = [0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_017 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 17) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 17) (g32p_literalTraceValue 46 17)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_017]
  decide +kernel

theorem g32p_row47_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 18 = [2] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 18) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 18) (g32p_literalTraceValue 46 18)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_018]
  decide +kernel

theorem g32p_row47_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 19 = [0, 4, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 19) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 19) (g32p_literalTraceValue 46 19)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_019]
  decide +kernel

theorem g32p_row47_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 20 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 20) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 20) (g32p_literalTraceValue 46 20)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_020]
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

theorem g32p_row47_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 23 = [0, 1, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 23) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 23) (g32p_literalTraceValue 46 23)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row47_traceCoefficients_023]
  decide +kernel

theorem g32p_row47_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 24 = [8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 24) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 24) (g32p_literalTraceValue 46 24)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_024]
  decide +kernel

theorem g32p_row47_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 25 = [0, 8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 25) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 25) (g32p_literalTraceValue 46 25)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_025]
  decide +kernel

theorem g32p_row47_traceCoefficients_027 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 27 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_027 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 27) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 27) (g32p_literalTraceValue 46 27)
      [1, 1, 1] [432] = true := by
  rw [g32p_row47_traceCoefficients_027]
  decide +kernel

theorem g32p_row47_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 28 = [4, 0, 1] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 28) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 28) (g32p_literalTraceValue 46 28)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row47_traceCoefficients_028]
  decide +kernel

theorem g32p_row47_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 29 = [0, 0, 8] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 29) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 29) (g32p_literalTraceValue 46 29)
      [1, 1, 1] [864] = true := by
  rw [g32p_row47_traceCoefficients_029]
  decide +kernel

theorem g32p_row47_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 31 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 31) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 31) (g32p_literalTraceValue 46 31)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row47_traceCoefficients_031]
  decide +kernel

theorem g32p_row47_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 32 = [4, 4] := by
  decide +kernel

theorem g32p_row47_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 32) 3
      (g32p_supplierTraceCoefficients g32p_row47_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row47_characterValues j)).val) 32) (g32p_literalTraceValue 46 32)
      [1, 1, 1] [] = true := by
  rw [g32p_row47_traceCoefficients_032]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
