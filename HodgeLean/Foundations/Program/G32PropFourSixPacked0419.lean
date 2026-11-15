import HodgeLean.Foundations.Program.G32PropFourSixPacked0418
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow37
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row36_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 94 = [4, 0, 0, 8] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 94) (g32p_literalTraceValue 35 94)
      [1, -1, 1] [2304, 2304] = true := by
  rw [g32p_row36_traceCoefficients_094]
  decide +kernel

theorem g32p_row36_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 96 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 96) (g32p_literalTraceValue 35 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row36_traceCoefficients_096]
  decide +kernel

theorem g32p_row36_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 97 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 97) (g32p_literalTraceValue 35 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row36_traceCoefficients_097]
  decide +kernel

theorem g32p_row36_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 99 = [1] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 99) (g32p_literalTraceValue 35 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row36_traceCoefficients_099]
  decide +kernel

theorem g32p_row36_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 101 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 101) (g32p_literalTraceValue 35 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row36_traceCoefficients_101]
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

def g32p_row36_generatorIndex : Fin 8 → Fin 408 :=
  ![35, 86, 137, 188, 274, 275, 376, 377]

theorem g32p_row36_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup26_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 35 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 35 g32p_row36_supplierClass
    g32p_row36_supplierClass_isConj g32p_supplierGroup26_support g32p_row36_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row36_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup26_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row36_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 35 c false (g32p_row36_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 35 c true (g32p_row36_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 35 c false (g32p_row36_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 35 c true (g32p_row36_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 35 c false (g32p_row36_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 35 c false (g32p_row36_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 35 c true (g32p_row36_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 35 c true (g32p_row36_coinduced_zero c hc true) 3

theorem g32p_row36_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row36_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row36_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row36_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row36_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row36_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row36_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row36_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row36_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row36_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row36_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row36_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row36_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup26_support →
      g32p_literalTraceValue (g32p_row36_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row36_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup26_support) :
    g32p_literalTraceValue (g32p_row36_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup26_support →
    g32p_literalTraceValue (g32p_row36_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row36_zeroTrace_block_00 r k
  · exact g32p_row36_zeroTrace_block_01 r k
  · exact g32p_row36_zeroTrace_block_02 r k
  · exact g32p_row36_zeroTrace_block_03 r k
  · exact g32p_row36_zeroTrace_block_04 r k
  · exact g32p_row36_zeroTrace_block_05 r k
  · exact g32p_row36_zeroTrace_block_06 r k

theorem g32p_row36_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup26_support) :
    (g32p_recordedInductionGenerators (g32p_row36_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row36_generatorIndex k) c) := by
  rw [g32p_row36_recordedGenerator_zero c hc k, g32p_row36_zeroTrace_arithmetic c k hc]
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

def g32p_row36_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else [2304, 2304]))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 6912, 6912] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [13824, 13824] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [-1152, 1152, 1152] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [-1152, 5760, 5760] else []) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [384, 384] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [0, 0, 384, 384] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [0, 0, 2304, 2304] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [384, 768, 768] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [-10368, 3456, 3456])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [6912, 6912] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [0, 0, 13824, 13824] else (if i.val < 84 then [0, 0, 2304, 2304] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [-1152, 1152, 1152] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else [2304, 2304]))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row36_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup26_support) :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) c) (g32p_literalTraceValue 35 c)
      [1, -1, 1] (g32p_row36_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row36_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_031
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_034
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_037
  · exact g32p_row36_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_049
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_057
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_082
  · exact g32p_row36_tracePolynomial_083
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_090
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_094
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_096
  · exact g32p_row36_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup26_support) hc)
  · exact g32p_row36_tracePolynomial_101

theorem g32p_row36_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 35 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 35 c) := by
  by_cases hc : c ∈ g32p_supplierGroup26_support
  · have hclass (j : Fin 384) :
        IsConj (g32p_literalRepresentative c) (g32p_row36_groupEquiv j : g32p_G) ↔
          g32p_row36_supplierClassifier j = c := by
      simpa only [g32p_row36_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row36_supplierClass_iff (g32p_row36_groupEquiv j) c
    have hχ (j : Fin 384) :
        (g32p_recordedSupplierCharacters 35 (g32p_row36_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row36_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 35 (show (g32p_recordedSuppliers 35).H from g32p_row36_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row36_characterValues (g32p_row36_groupEquiv.symm (g32p_row36_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 35).H (g32p_recordedSupplierCharacters 35)
      (g32p_literalRepresentative c) g32p_row36_groupEquiv g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) c 6 384
      (g32p_literalCentralizer c) (g32p_literalTraceValue 35 c) [1, -1, 1]
      (g32p_row36_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row36_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 35)))
      (g32p_row36_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row36_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row36_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
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

theorem g32p_row36_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
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

theorem g32p_row36_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
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

theorem g32p_row36_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
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

theorem g32p_row36_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
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

theorem g32p_row36_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
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

theorem g32p_row36_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row36_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row36_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
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

theorem g32p_row36_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row36_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row36_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row36_variantArithmetic_00_0 r
  · exact g32p_row36_variantArithmetic_01_0 r
  · exact g32p_row36_variantArithmetic_02_0 r
  · exact g32p_row36_variantArithmetic_03_0 r
  · exact g32p_row36_variantArithmetic_04_0 r
  · exact g32p_row36_variantArithmetic_05_0 r
  · exact g32p_row36_variantArithmetic_06_0 r

theorem g32p_row36_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row36_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row36_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row36_variantArithmetic_00_1 r
  · exact g32p_row36_variantArithmetic_01_1 r
  · exact g32p_row36_variantArithmetic_02_1 r
  · exact g32p_row36_variantArithmetic_03_1 r
  · exact g32p_row36_variantArithmetic_04_1 r
  · exact g32p_row36_variantArithmetic_05_1 r
  · exact g32p_row36_variantArithmetic_06_1 r

theorem g32p_row36_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row36_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row36_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row36_variantArithmetic_00_2 r
  · exact g32p_row36_variantArithmetic_01_2 r
  · exact g32p_row36_variantArithmetic_02_2 r
  · exact g32p_row36_variantArithmetic_03_2 r
  · exact g32p_row36_variantArithmetic_04_2 r
  · exact g32p_row36_variantArithmetic_05_2 r
  · exact g32p_row36_variantArithmetic_06_2 r

theorem g32p_row36_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row36_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row36_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row36_variantArithmetic_00_3 r
  · exact g32p_row36_variantArithmetic_01_3 r
  · exact g32p_row36_variantArithmetic_02_3 r
  · exact g32p_row36_variantArithmetic_03_3 r
  · exact g32p_row36_variantArithmetic_04_3 r
  · exact g32p_row36_variantArithmetic_05_3 r
  · exact g32p_row36_variantArithmetic_06_3 r

theorem g32p_row36_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row36_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row36_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row36_variantArithmetic_00_4 r
  · exact g32p_row36_variantArithmetic_01_4 r
  · exact g32p_row36_variantArithmetic_02_4 r
  · exact g32p_row36_variantArithmetic_03_4 r
  · exact g32p_row36_variantArithmetic_04_4 r
  · exact g32p_row36_variantArithmetic_05_4 r
  · exact g32p_row36_variantArithmetic_06_4 r

theorem g32p_row36_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row36_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row36_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row36_variantArithmetic_00_5 r
  · exact g32p_row36_variantArithmetic_01_5 r
  · exact g32p_row36_variantArithmetic_02_5 r
  · exact g32p_row36_variantArithmetic_03_5 r
  · exact g32p_row36_variantArithmetic_04_5 r
  · exact g32p_row36_variantArithmetic_05_5 r
  · exact g32p_row36_variantArithmetic_06_5 r

theorem g32p_row36_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row36_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row36_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row36_variantArithmetic_00_6 r
  · exact g32p_row36_variantArithmetic_01_6 r
  · exact g32p_row36_variantArithmetic_02_6 r
  · exact g32p_row36_variantArithmetic_03_6 r
  · exact g32p_row36_variantArithmetic_04_6 r
  · exact g32p_row36_variantArithmetic_05_6 r
  · exact g32p_row36_variantArithmetic_06_6 r

theorem g32p_row36_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row36_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row36_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 35 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row36_variantArithmetic_00_7 r
  · exact g32p_row36_variantArithmetic_01_7 r
  · exact g32p_row36_variantArithmetic_02_7 r
  · exact g32p_row36_variantArithmetic_03_7 r
  · exact g32p_row36_variantArithmetic_04_7 r
  · exact g32p_row36_variantArithmetic_05_7 r
  · exact g32p_row36_variantArithmetic_06_7 r

theorem g32p_row36_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row36_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row36_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 35 c _ (g32p_row36_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row36_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 35 c _ (g32p_row36_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row36_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 35 c _ (g32p_row36_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row36_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 35 c _ (g32p_row36_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row36_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 35 c _ (g32p_row36_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row36_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 35 c _ (g32p_row36_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row36_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 35 c _ (g32p_row36_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row36_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 35 c _ (g32p_row36_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row36_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup27_source : Fin 144 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (85, 24)) else (if i.val < 3 then (57, 102) else (30, 187))) else (if i.val < 6 then (if i.val < 5 then (2, 20) else (10, 83)) else (if i.val < 7 then (25, 127) else (if i.val < 8 then (14, 196) else (104, 121))))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then (30, 40) else (116, 114)) else (if i.val < 12 then (80, 106) else (10, 188))) else (if i.val < 15 then (if i.val < 14 then (14, 92) else (7, 126)) else (if i.val < 16 then (80, 162) else (if i.val < 17 then (139, 230) else (108, 233)))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then (5, 174) else (6, 197)) else (if i.val < 21 then (34, 153) else (14, 160))) else (if i.val < 24 then (if i.val < 23 then (2, 80) else (43, 197)) else (if i.val < 25 then (0, 99) else (if i.val < 26 then (142, 61) else (72, 165))))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then (79, 184) else (113, 138)) else (if i.val < 30 then (122, 249) else (133, 164))) else (if i.val < 33 then (if i.val < 32 then (38, 183) else (129, 178)) else (if i.val < 34 then (11, 232) else (if i.val < 35 then (134, 33) else (92, 159))))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then (78, 149) else (66, 165)) else (if i.val < 39 then (128, 104) else (4, 175))) else (if i.val < 42 then (if i.val < 41 then (86, 197) else (100, 213)) else (if i.val < 43 then (77, 90) else (if i.val < 44 then (16, 50) else (109, 158))))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then (17, 118) else (6, 150)) else (if i.val < 48 then (46, 127) else (33, 13))) else (if i.val < 51 then (if i.val < 50 then (17, 125) else (5, 167)) else (if i.val < 52 then (14, 242) else (if i.val < 53 then (88, 169) else (19, 118)))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then (125, 211) else (55, 220)) else (if i.val < 57 then (33, 14) else (111, 107))) else (if i.val < 60 then (if i.val < 59 then (14, 199) else (93, 230)) else (if i.val < 61 then (73, 44) else (if i.val < 62 then (6, 63) else (132, 52))))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then (78, 220) else (9, 67)) else (if i.val < 66 then (105, 150) else (128, 62))) else (if i.val < 69 then (if i.val < 68 then (54, 139) else (57, 187)) else (if i.val < 70 then (132, 186) else (if i.val < 71 then (47, 194) else (62, 120)))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then (103, 122) else (37, 183)) else (if i.val < 75 then (50, 241) else (109, 218))) else (if i.val < 78 then (if i.val < 77 then (76, 251) else (11, 114)) else (if i.val < 79 then (114, 206) else (if i.val < 80 then (53, 94) else (114, 122))))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then (132, 76) else (107, 123)) else (if i.val < 84 then (130, 215) else (25, 141))) else (if i.val < 87 then (if i.val < 86 then (8, 51) else (142, 0)) else (if i.val < 88 then (123, 177) else (if i.val < 89 then (80, 54) else (120, 4)))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then (131, 36) else (28, 204)) else (if i.val < 93 then (124, 87) else (98, 241))) else (if i.val < 96 then (if i.val < 95 then (101, 160) else (87, 24)) else (if i.val < 97 then (47, 219) else (if i.val < 98 then (109, 62) else (7, 237))))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then (8, 138) else (14, 235)) else (if i.val < 102 then (6, 62) else (102, 87))) else (if i.val < 105 then (if i.val < 104 then (28, 95) else (13, 65)) else (if i.val < 106 then (32, 89) else (if i.val < 107 then (136, 67) else (5, 246))))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then (31, 115) else (19, 222)) else (if i.val < 111 then (66, 104) else (77, 197))) else (if i.val < 114 then (if i.val < 113 then (115, 207) else (89, 218)) else (if i.val < 115 then (115, 118) else (if i.val < 116 then (118, 245) else (32, 141))))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then (119, 233) else (36, 151)) else (if i.val < 120 then (135, 162) else (135, 94))) else (if i.val < 123 then (if i.val < 122 then (143, 73) else (118, 113)) else (if i.val < 124 then (54, 174) else (if i.val < 125 then (131, 207) else (48, 12)))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then (34, 112) else (124, 39)) else (if i.val < 129 then (25, 39) else (116, 108))) else (if i.val < 132 then (if i.val < 131 then (58, 255) else (25, 18)) else (if i.val < 133 then (91, 212) else (if i.val < 134 then (59, 160) else (74, 244))))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then (15, 125) else (57, 159)) else (if i.val < 138 then (96, 11) else (6, 234))) else (if i.val < 141 then (if i.val < 140 then (120, 3) else (130, 70)) else (if i.val < 142 then (143, 62) else (if i.val < 143 then (120, 165) else (92, 88)))))))))

def g32p_supplierGroup27_classify : Fin 144 → Fin 102 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 92) else (if i.val < 3 then 5 else 94)) else (if i.val < 6 then (if i.val < 5 then 1 else 18) else (if i.val < 7 then 11 else (if i.val < 8 then 92 else 29)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 95 else 29) else (if i.val < 12 then 92 else 18)) else (if i.val < 15 then (if i.val < 14 then 94 else 8) else (if i.val < 16 then 94 else (if i.val < 17 then 29 else 94))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then 98 else 5) else (if i.val < 21 then 8 else 98)) else (if i.val < 24 then (if i.val < 23 then 2 else 81) else (if i.val < 25 then 99 else (if i.val < 26 then 25 else 56)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then 35 else 25) else (if i.val < 30 then 25 else 29)) else (if i.val < 33 then (if i.val < 32 then 4 else 72) else (if i.val < 34 then 56 else (if i.val < 35 then 29 else 7)))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then 92 else 72) else (if i.val < 39 then 7 else 84)) else (if i.val < 42 then (if i.val < 41 then 23 else 25) else (if i.val < 43 then 29 else (if i.val < 44 then 5 else 94)))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then 8 else 4) else (if i.val < 48 then 81 else 5)) else (if i.val < 51 then (if i.val < 50 then 8 else 98) else (if i.val < 52 then 2 else (if i.val < 53 then 56 else 4))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then 29 else 98) else (if i.val < 57 then 5 else 81)) else (if i.val < 60 then (if i.val < 59 then 89 else 72) else (if i.val < 61 then 81 else (if i.val < 62 then 2 else 7)))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then 89 else 2) else (if i.val < 66 then 89 else 89)) else (if i.val < 69 then (if i.val < 68 then 94 else 5) else (if i.val < 70 then 25 else (if i.val < 71 then 25 else 35))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 66 else 35) else (if i.val < 75 then 66 else 76)) else (if i.val < 78 then (if i.val < 77 then 66 else 11) else (if i.val < 79 then 29 else (if i.val < 80 then 79 else 25)))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then 7 else 67) else (if i.val < 84 then 86 else 56)) else (if i.val < 87 then (if i.val < 86 then 11 else 7) else (if i.val < 88 then 45 else (if i.val < 89 then 35 else 7))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then 86 else 66) else (if i.val < 93 then 45 else 86)) else (if i.val < 96 then (if i.val < 95 then 45 else 10) else (if i.val < 97 then 11 else (if i.val < 98 then 72 else 1)))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then 4 else 1) else (if i.val < 102 then 3 else 25)) else (if i.val < 105 then (if i.val < 104 then 93 else 93) else (if i.val < 106 then 3 else (if i.val < 107 then 72 else 1)))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 93 else 3) else (if i.val < 111 then 72 else 93)) else (if i.val < 114 then (if i.val < 113 then 15 else 32) else (if i.val < 115 then 32 else (if i.val < 116 then 20 else 32)))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 41 else 32) else (if i.val < 120 then 20 else 41)) else (if i.val < 123 then (if i.val < 122 then 20 else 41) else (if i.val < 124 then 77 else (if i.val < 125 then 15 else 86))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then 10 else 45) else (if i.val < 129 then 84 else 15)) else (if i.val < 132 then (if i.val < 131 then 10 else 84) else (if i.val < 133 then 15 else (if i.val < 134 then 10 else 84)))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then 3 else 19) else (if i.val < 138 then 41 else 44)) else (if i.val < 141 then (if i.val < 140 then 20 else 41) else (if i.val < 142 then 20 else (if i.val < 143 then 41 else 20))))))))

def g32p_supplierGroup27_support : Finset (Fin 102) :=
  {0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 15, 18, 19, 20, 23, 25, 29, 32, 35, 41, 44, 45, 56, 66, 67, 72, 76, 77, 79, 81, 84, 86, 89, 92, 93, 94, 95, 98, 99}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup27_matrix_000 : ∀ r : Fin 16,
    g32p_row37_groupNodes (g32p_finBlockIndex 144 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 0 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup27_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 0 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 0 r)).2 =
      g32p_supplierGroup27_classify (g32p_finBlockIndex 144 0 r) := by
  decide +kernel

theorem g32p_supplierGroup27_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup27_classify (g32p_finBlockIndex 144 0 r) ∈ g32p_supplierGroup27_support := by
  decide +kernel

theorem g32p_supplierGroup27_matrix_001 : ∀ r : Fin 16,
    g32p_row37_groupNodes (g32p_finBlockIndex 144 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 1 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup27_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 1 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 1 r)).2 =
      g32p_supplierGroup27_classify (g32p_finBlockIndex 144 1 r) := by
  decide +kernel

theorem g32p_supplierGroup27_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup27_classify (g32p_finBlockIndex 144 1 r) ∈ g32p_supplierGroup27_support := by
  decide +kernel

theorem g32p_supplierGroup27_matrix_002 : ∀ r : Fin 16,
    g32p_row37_groupNodes (g32p_finBlockIndex 144 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 2 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup27_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 2 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 2 r)).2 =
      g32p_supplierGroup27_classify (g32p_finBlockIndex 144 2 r) := by
  decide +kernel

theorem g32p_supplierGroup27_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup27_classify (g32p_finBlockIndex 144 2 r) ∈ g32p_supplierGroup27_support := by
  decide +kernel

theorem g32p_supplierGroup27_matrix_003 : ∀ r : Fin 16,
    g32p_row37_groupNodes (g32p_finBlockIndex 144 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 3 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup27_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 3 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 3 r)).2 =
      g32p_supplierGroup27_classify (g32p_finBlockIndex 144 3 r) := by
  decide +kernel

theorem g32p_supplierGroup27_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup27_classify (g32p_finBlockIndex 144 3 r) ∈ g32p_supplierGroup27_support := by
  decide +kernel

theorem g32p_supplierGroup27_matrix_004 : ∀ r : Fin 16,
    g32p_row37_groupNodes (g32p_finBlockIndex 144 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 4 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup27_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 4 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 4 r)).2 =
      g32p_supplierGroup27_classify (g32p_finBlockIndex 144 4 r) := by
  decide +kernel

theorem g32p_supplierGroup27_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup27_classify (g32p_finBlockIndex 144 4 r) ∈ g32p_supplierGroup27_support := by
  decide +kernel

theorem g32p_supplierGroup27_matrix_005 : ∀ r : Fin 16,
    g32p_row37_groupNodes (g32p_finBlockIndex 144 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 5 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup27_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 5 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 5 r)).2 =
      g32p_supplierGroup27_classify (g32p_finBlockIndex 144 5 r) := by
  decide +kernel

theorem g32p_supplierGroup27_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup27_classify (g32p_finBlockIndex 144 5 r) ∈ g32p_supplierGroup27_support := by
  decide +kernel

theorem g32p_supplierGroup27_matrix_006 : ∀ r : Fin 16,
    g32p_row37_groupNodes (g32p_finBlockIndex 144 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 6 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup27_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 6 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 6 r)).2 =
      g32p_supplierGroup27_classify (g32p_finBlockIndex 144 6 r) := by
  decide +kernel

theorem g32p_supplierGroup27_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup27_classify (g32p_finBlockIndex 144 6 r) ∈ g32p_supplierGroup27_support := by
  decide +kernel

theorem g32p_supplierGroup27_matrix_007 : ∀ r : Fin 16,
    g32p_row37_groupNodes (g32p_finBlockIndex 144 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 7 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup27_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 7 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 7 r)).2 =
      g32p_supplierGroup27_classify (g32p_finBlockIndex 144 7 r) := by
  decide +kernel

theorem g32p_supplierGroup27_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup27_classify (g32p_finBlockIndex 144 7 r) ∈ g32p_supplierGroup27_support := by
  decide +kernel

theorem g32p_supplierGroup27_matrix_008 : ∀ r : Fin 16,
    g32p_row37_groupNodes (g32p_finBlockIndex 144 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 8 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup27_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup27_source (g32p_finBlockIndex 144 8 r)).1 (g32p_supplierGroup27_source (g32p_finBlockIndex 144 8 r)).2 =
      g32p_supplierGroup27_classify (g32p_finBlockIndex 144 8 r) := by
  decide +kernel

theorem g32p_supplierGroup27_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup27_classify (g32p_finBlockIndex 144 8 r) ∈ g32p_supplierGroup27_support := by
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

theorem g32p_supplierGroup27_matrix (i : Fin 144) :
    g32p_row37_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source i).1 (g32p_supplierGroup27_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row37_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup27_source i).1 (g32p_supplierGroup27_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup27_matrix_000 r
  · exact g32p_supplierGroup27_matrix_001 r
  · exact g32p_supplierGroup27_matrix_002 r
  · exact g32p_supplierGroup27_matrix_003 r
  · exact g32p_supplierGroup27_matrix_004 r
  · exact g32p_supplierGroup27_matrix_005 r
  · exact g32p_supplierGroup27_matrix_006 r
  · exact g32p_supplierGroup27_matrix_007 r
  · exact g32p_supplierGroup27_matrix_008 r

theorem g32p_supplierGroup27_class (i : Fin 144) :
    g32p_supplierForest_classes (g32p_supplierGroup27_source i).1 (g32p_supplierGroup27_source i).2 =
      g32p_supplierGroup27_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup27_source i).1 (g32p_supplierGroup27_source i).2 =
      g32p_supplierGroup27_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup27_class_000 r
  · exact g32p_supplierGroup27_class_001 r
  · exact g32p_supplierGroup27_class_002 r
  · exact g32p_supplierGroup27_class_003 r
  · exact g32p_supplierGroup27_class_004 r
  · exact g32p_supplierGroup27_class_005 r
  · exact g32p_supplierGroup27_class_006 r
  · exact g32p_supplierGroup27_class_007 r
  · exact g32p_supplierGroup27_class_008 r

theorem g32p_supplierGroup27_support_mem (i : Fin 144) :
    g32p_supplierGroup27_classify i ∈ g32p_supplierGroup27_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup27_classify i ∈ g32p_supplierGroup27_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup27_support_000 r
  · exact g32p_supplierGroup27_support_001 r
  · exact g32p_supplierGroup27_support_002 r
  · exact g32p_supplierGroup27_support_003 r
  · exact g32p_supplierGroup27_support_004 r
  · exact g32p_supplierGroup27_support_005 r
  · exact g32p_supplierGroup27_support_006 r
  · exact g32p_supplierGroup27_support_007 r
  · exact g32p_supplierGroup27_support_008 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row37_supplierClassifier : Fin 144 → Fin 102 := g32p_supplierGroup27_classify

theorem g32p_row37_groupEquiv_isConj (i : Fin 144) :
    IsConj (g32p_row37_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row37_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup27_source i).1 (g32p_supplierGroup27_source i).2
  rw [g32p_supplierGroup27_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row37_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup27_matrix i)

def g32p_row37_supplierClass (h : (g32p_recordedSuppliers 36).H) : Fin 102 :=
  g32p_row37_supplierClassifier (g32p_row37_groupEquiv.symm h)

theorem g32p_row37_supplierClass_isConj (h : (g32p_recordedSuppliers 36).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row37_supplierClass h)) := by
  have he : (g32p_row37_groupEquiv (g32p_row37_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 36).H => (a : g32p_G))
      (g32p_row37_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row37_supplierClassifier (g32p_row37_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row37_groupEquiv_isConj (g32p_row37_groupEquiv.symm h)

theorem g32p_row37_supplierClass_iff (h : (g32p_recordedSuppliers 36).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row37_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row37_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row37_supplierClass_isConj h).symm

theorem g32p_row37_supplierClass_mem_support (h : (g32p_recordedSuppliers 36).H) :
    g32p_row37_supplierClass h ∈ g32p_supplierGroup27_support :=
  g32p_supplierGroup27_support_mem (g32p_row37_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row37_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 0) (g32p_literalTraceValue 36 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_000]
  decide +kernel

theorem g32p_row37_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 1 = [4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 1) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 1) (g32p_literalTraceValue 36 1)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_001]
  decide +kernel

theorem g32p_row37_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 2 = [4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 2) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 2) (g32p_literalTraceValue 36 2)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_002]
  decide +kernel

theorem g32p_row37_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 3 = [4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 3) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 3) (g32p_literalTraceValue 36 3)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_003]
  decide +kernel

theorem g32p_row37_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 4 = [0, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 4) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 4) (g32p_literalTraceValue 36 4)
      [1, -1, 1] [2592, 2592, 2592] = true := by
  rw [g32p_row37_traceCoefficients_004]
  decide +kernel

theorem g32p_row37_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 5 = [6] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 5) (g32p_literalTraceValue 36 5)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_005]
  decide +kernel

theorem g32p_row37_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 7 = [0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 7) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 7) (g32p_literalTraceValue 36 7)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row37_traceCoefficients_007]
  decide +kernel

theorem g32p_row37_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 8 = [4] := by
  decide +kernel

theorem g32p_row37_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 8) 6
      (g32p_supplierTraceCoefficients g32p_row37_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row37_characterValues j)).val) 8) (g32p_literalTraceValue 36 8)
      [1, -1, 1] [] = true := by
  rw [g32p_row37_traceCoefficients_008]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
