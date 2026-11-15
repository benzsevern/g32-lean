import HodgeLean.Foundations.Program.G32PropFourSixPacked0399
import HodgeLean.Foundations.Program.G32PropFourSixPacked0397
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0398
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow26
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row25_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 96) (g32p_literalTraceValue 24 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row25_traceCoefficients_096]
  decide +kernel

theorem g32p_row25_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 97) (g32p_literalTraceValue 24 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row25_traceCoefficients_097]
  decide +kernel

theorem g32p_row25_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 99) (g32p_literalTraceValue 24 99)
      [1, -1, 1] [] = true := by
  rw [g32p_row25_traceCoefficients_099]
  decide +kernel

theorem g32p_row25_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) 101) (g32p_literalTraceValue 24 101)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row25_traceCoefficients_101]
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

def g32p_row25_generatorIndex : Fin 8 → Fin 408 :=
  ![24, 75, 126, 177, 252, 253, 354, 355]

theorem g32p_row25_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup17_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 24 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 24 g32p_row25_supplierClass
    g32p_row25_supplierClass_isConj g32p_supplierGroup17_support g32p_row25_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row25_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup17_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row25_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 24 c false (g32p_row25_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 24 c true (g32p_row25_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 24 c false (g32p_row25_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 24 c true (g32p_row25_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 24 c false (g32p_row25_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 24 c false (g32p_row25_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 24 c true (g32p_row25_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 24 c true (g32p_row25_coinduced_zero c hc true) 3

theorem g32p_row25_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row25_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row25_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row25_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row25_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row25_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row25_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row25_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row25_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row25_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row25_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row25_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row25_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup17_support →
      g32p_literalTraceValue (g32p_row25_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row25_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup17_support) :
    g32p_literalTraceValue (g32p_row25_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup17_support →
    g32p_literalTraceValue (g32p_row25_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row25_zeroTrace_block_00 r k
  · exact g32p_row25_zeroTrace_block_01 r k
  · exact g32p_row25_zeroTrace_block_02 r k
  · exact g32p_row25_zeroTrace_block_03 r k
  · exact g32p_row25_zeroTrace_block_04 r k
  · exact g32p_row25_zeroTrace_block_05 r k
  · exact g32p_row25_zeroTrace_block_06 r k

theorem g32p_row25_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup17_support) :
    (g32p_recordedInductionGenerators (g32p_row25_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row25_generatorIndex k) c) := by
  rw [g32p_row25_recordedGenerator_zero c hc k, g32p_row25_zeroTrace_arithmetic c k hc]
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

def g32p_row25_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [5184, 5184, 5184] else [3456, 3456]))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [0, 0, 3456, 3456] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [6912, 6912] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [0, 0, 1728, 1728] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [-1728] else [576, 576, 576]))) else (if i.val < 34 then (if i.val < 32 then [-3456] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [5760, 9216, 9216] else []) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [576, 576] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else [1728, 1728]))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [0, 0, 576, 576] else [0, 0, 1728, 1728])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [0, 0, 3456, 3456] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [0, 576, 576] else (if i.val < 59 then [] else [-1728])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [3456, 10368, 10368])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [3456, 3456] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [1728, 1728] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [0, 0, 6912, 6912] else (if i.val < 84 then [0, 0, 3456, 3456] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [-3456] else [])) else (if i.val < 93 then [5184, 5184, 5184] else (if i.val < 94 then [] else [3456, 3456]))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row25_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup17_support) :
    g32p_supplierTracePolynomialCheck 576 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) c) (g32p_literalTraceValue 24 c)
      [1, -1, 1] (g32p_row25_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row25_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_004
  · exact g32p_row25_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_021
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_024
  · exact g32p_row25_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_029
  · exact g32p_row25_tracePolynomial_030
  · exact g32p_row25_tracePolynomial_031
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_034
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_037
  · exact g32p_row25_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_043
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_046
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_049
  · exact g32p_row25_tracePolynomial_050
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_056
  · exact g32p_row25_tracePolynomial_057
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_074
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_082
  · exact g32p_row25_tracePolynomial_083
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_090
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_092
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_094
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_096
  · exact g32p_row25_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup17_support) hc)
  · exact g32p_row25_tracePolynomial_101

theorem g32p_row25_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 24 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 24 c) := by
  by_cases hc : c ∈ g32p_supplierGroup17_support
  · have hclass (j : Fin 576) :
        IsConj (g32p_literalRepresentative c) (g32p_row22_groupEquiv j : g32p_G) ↔
          g32p_row25_supplierClassifier j = c := by
      simpa only [g32p_row25_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row25_supplierClass_iff (g32p_row22_groupEquiv j) c
    have hχ (j : Fin 576) :
        (g32p_recordedSupplierCharacters 24 (g32p_row22_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row25_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 24 (show (g32p_recordedSuppliers 24).H from g32p_row22_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row25_characterValues (g32p_row22_groupEquiv.symm (g32p_row22_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 24).H (g32p_recordedSupplierCharacters 24)
      (g32p_literalRepresentative c) g32p_row22_groupEquiv g32p_row25_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row25_characterValues j)).val) c 6 576
      (g32p_literalCentralizer c) (g32p_literalTraceValue 24 c) [1, -1, 1]
      (g32p_row25_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row25_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 24)))
      (g32p_row25_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row25_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row25_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
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

theorem g32p_row25_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
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

theorem g32p_row25_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
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

theorem g32p_row25_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
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

theorem g32p_row25_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
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

theorem g32p_row25_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
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

theorem g32p_row25_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row25_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row25_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
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

theorem g32p_row25_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row25_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row25_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row25_variantArithmetic_00_0 r
  · exact g32p_row25_variantArithmetic_01_0 r
  · exact g32p_row25_variantArithmetic_02_0 r
  · exact g32p_row25_variantArithmetic_03_0 r
  · exact g32p_row25_variantArithmetic_04_0 r
  · exact g32p_row25_variantArithmetic_05_0 r
  · exact g32p_row25_variantArithmetic_06_0 r

theorem g32p_row25_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row25_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row25_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row25_variantArithmetic_00_1 r
  · exact g32p_row25_variantArithmetic_01_1 r
  · exact g32p_row25_variantArithmetic_02_1 r
  · exact g32p_row25_variantArithmetic_03_1 r
  · exact g32p_row25_variantArithmetic_04_1 r
  · exact g32p_row25_variantArithmetic_05_1 r
  · exact g32p_row25_variantArithmetic_06_1 r

theorem g32p_row25_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row25_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row25_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row25_variantArithmetic_00_2 r
  · exact g32p_row25_variantArithmetic_01_2 r
  · exact g32p_row25_variantArithmetic_02_2 r
  · exact g32p_row25_variantArithmetic_03_2 r
  · exact g32p_row25_variantArithmetic_04_2 r
  · exact g32p_row25_variantArithmetic_05_2 r
  · exact g32p_row25_variantArithmetic_06_2 r

theorem g32p_row25_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row25_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row25_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row25_variantArithmetic_00_3 r
  · exact g32p_row25_variantArithmetic_01_3 r
  · exact g32p_row25_variantArithmetic_02_3 r
  · exact g32p_row25_variantArithmetic_03_3 r
  · exact g32p_row25_variantArithmetic_04_3 r
  · exact g32p_row25_variantArithmetic_05_3 r
  · exact g32p_row25_variantArithmetic_06_3 r

theorem g32p_row25_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row25_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row25_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row25_variantArithmetic_00_4 r
  · exact g32p_row25_variantArithmetic_01_4 r
  · exact g32p_row25_variantArithmetic_02_4 r
  · exact g32p_row25_variantArithmetic_03_4 r
  · exact g32p_row25_variantArithmetic_04_4 r
  · exact g32p_row25_variantArithmetic_05_4 r
  · exact g32p_row25_variantArithmetic_06_4 r

theorem g32p_row25_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row25_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row25_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row25_variantArithmetic_00_5 r
  · exact g32p_row25_variantArithmetic_01_5 r
  · exact g32p_row25_variantArithmetic_02_5 r
  · exact g32p_row25_variantArithmetic_03_5 r
  · exact g32p_row25_variantArithmetic_04_5 r
  · exact g32p_row25_variantArithmetic_05_5 r
  · exact g32p_row25_variantArithmetic_06_5 r

theorem g32p_row25_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row25_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row25_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row25_variantArithmetic_00_6 r
  · exact g32p_row25_variantArithmetic_01_6 r
  · exact g32p_row25_variantArithmetic_02_6 r
  · exact g32p_row25_variantArithmetic_03_6 r
  · exact g32p_row25_variantArithmetic_04_6 r
  · exact g32p_row25_variantArithmetic_05_6 r
  · exact g32p_row25_variantArithmetic_06_6 r

theorem g32p_row25_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row25_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row25_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 24 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row25_variantArithmetic_00_7 r
  · exact g32p_row25_variantArithmetic_01_7 r
  · exact g32p_row25_variantArithmetic_02_7 r
  · exact g32p_row25_variantArithmetic_03_7 r
  · exact g32p_row25_variantArithmetic_04_7 r
  · exact g32p_row25_variantArithmetic_05_7 r
  · exact g32p_row25_variantArithmetic_06_7 r

theorem g32p_row25_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row25_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row25_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 24 c _ (g32p_row25_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row25_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 24 c _ (g32p_row25_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row25_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 24 c _ (g32p_row25_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row25_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 24 c _ (g32p_row25_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row25_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 24 c _ (g32p_row25_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row25_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 24 c _ (g32p_row25_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row25_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 24 c _ (g32p_row25_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row25_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 24 c _ (g32p_row25_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row25_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup20_source : Fin 576 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 288 then (if i.val < 144 then (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (111, 215)) else (if i.val < 3 then (97, 85) else (83, 137))) else (if i.val < 6 then (if i.val < 5 then (0, 2) else (0, 99)) else (if i.val < 7 then (26, 119) else (if i.val < 8 then (67, 137) else (103, 195))))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then (56, 0) else (62, 15)) else (if i.val < 12 then (48, 196) else (25, 179))) else (if i.val < 15 then (if i.val < 14 then (118, 52) else (84, 151)) else (if i.val < 16 then (55, 155) else (if i.val < 17 then (13, 191) else (131, 141)))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then (86, 220) else (84, 215)) else (if i.val < 21 then (0, 1) else (31, 172))) else (if i.val < 24 then (if i.val < 23 then (92, 89) else (56, 51)) else (if i.val < 25 then (12, 27) else (if i.val < 26 then (53, 57) else (25, 130))))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then (31, 11) else (41, 6)) else (if i.val < 30 then (79, 211) else (22, 50))) else (if i.val < 33 then (if i.val < 32 then (22, 11) else (36, 24)) else (if i.val < 34 then (121, 120) else (if i.val < 35 then (8, 190) else (83, 87))))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then (56, 134) else (59, 19)) else (if i.val < 39 then (129, 54) else (61, 59))) else (if i.val < 42 then (if i.val < 41 then (99, 14) else (13, 54)) else (if i.val < 43 then (61, 118) else (if i.val < 44 then (111, 116) else (96, 114))))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then (74, 199) else (102, 215)) else (if i.val < 48 then (133, 242) else (83, 81))) else (if i.val < 51 then (if i.val < 50 then (130, 0) else (97, 71)) else (if i.val < 52 then (140, 230) else (if i.val < 53 then (105, 47) else (52, 183)))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then (99, 208) else (31, 82)) else (if i.val < 57 then (142, 109) else (31, 186))) else (if i.val < 60 then (if i.val < 59 then (35, 114) else (14, 206)) else (if i.val < 61 then (1, 175) else (if i.val < 62 then (0, 101) else (44, 21))))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then (40, 131) else (35, 194)) else (if i.val < 66 then (30, 48) else (19, 80))) else (if i.val < 69 then (if i.val < 68 then (111, 62) else (36, 200)) else (if i.val < 70 then (61, 90) else (if i.val < 71 then (0, 97) else (96, 71)))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then (124, 88) else (19, 70)) else (if i.val < 75 then (139, 200) else (23, 79))) else (if i.val < 78 then (if i.val < 77 then (76, 207) else (34, 216)) else (if i.val < 79 then (29, 158) else (if i.val < 80 then (132, 202) else (6, 43))))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then (53, 90) else (90, 12)) else (if i.val < 84 then (23, 34) else (130, 174))) else (if i.val < 87 then (if i.val < 86 then (74, 33) else (115, 134)) else (if i.val < 88 then (89, 188) else (if i.val < 89 then (53, 103) else (103, 46)))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then (3, 8) else (56, 119)) else (if i.val < 93 then (132, 19) else (107, 106))) else (if i.val < 96 then (if i.val < 95 then (87, 63) else (14, 190)) else (if i.val < 97 then (68, 72) else (if i.val < 98 then (37, 125) else (22, 13))))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then (0, 96) else (33, 31)) else (if i.val < 102 then (127, 66) else (10, 190))) else (if i.val < 105 then (if i.val < 104 then (33, 83) else (113, 255)) else (if i.val < 106 then (84, 253) else (if i.val < 107 then (54, 85) else (67, 150))))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then (1, 122) else (88, 65)) else (if i.val < 111 then (111, 179) else (110, 24))) else (if i.val < 114 then (if i.val < 113 then (3, 16) else (91, 129)) else (if i.val < 115 then (104, 36) else (if i.val < 116 then (108, 86) else (110, 88))))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then (116, 121) else (98, 247)) else (if i.val < 120 then (111, 161) else (134, 11))) else (if i.val < 123 then (if i.val < 122 then (80, 110) else (93, 151)) else (if i.val < 124 then (139, 238) else (if i.val < 125 then (16, 65) else (17, 92)))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then (47, 126) else (104, 255)) else (if i.val < 129 then (118, 156) else (87, 214))) else (if i.val < 132 then (if i.val < 131 then (96, 29) else (142, 46)) else (if i.val < 133 then (5, 178) else (if i.val < 134 then (111, 219) else (16, 156))))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then (85, 75) else (39, 226)) else (if i.val < 138 then (84, 189) else (85, 88))) else (if i.val < 141 then (if i.val < 140 then (56, 155) else (0, 37)) else (if i.val < 142 then (15, 62) else (if i.val < 143 then (92, 103) else (75, 8))))))))) else (if i.val < 216 then (if i.val < 180 then (if i.val < 162 then (if i.val < 153 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then (59, 127) else (111, 239)) else (if i.val < 147 then (61, 73) else (10, 200))) else (if i.val < 150 then (if i.val < 149 then (5, 191) else (58, 83)) else (if i.val < 151 then (5, 22) else (if i.val < 152 then (84, 234) else (114, 13))))) else (if i.val < 157 then (if i.val < 155 then (if i.val < 154 then (56, 43) else (93, 193)) else (if i.val < 156 then (141, 81) else (88, 62))) else (if i.val < 159 then (if i.val < 158 then (88, 44) else (111, 184)) else (if i.val < 160 then (30, 218) else (if i.val < 161 then (5, 120) else (116, 51)))))) else (if i.val < 171 then (if i.val < 166 then (if i.val < 164 then (if i.val < 163 then (103, 253) else (129, 2)) else (if i.val < 165 then (34, 33) else (1, 143))) else (if i.val < 168 then (if i.val < 167 then (88, 27) else (49, 145)) else (if i.val < 169 then (32, 202) else (if i.val < 170 then (18, 212) else (121, 78))))) else (if i.val < 175 then (if i.val < 173 then (if i.val < 172 then (49, 242) else (18, 222)) else (if i.val < 174 then (119, 156) else (75, 146))) else (if i.val < 177 then (if i.val < 176 then (13, 103) else (5, 37)) else (if i.val < 178 then (10, 50) else (if i.val < 179 then (112, 146) else (111, 31))))))) else (if i.val < 198 then (if i.val < 189 then (if i.val < 184 then (if i.val < 182 then (if i.val < 181 then (125, 200) else (29, 51)) else (if i.val < 183 then (114, 134) else (100, 2))) else (if i.val < 186 then (if i.val < 185 then (103, 85) else (140, 224)) else (if i.val < 187 then (87, 92) else (if i.val < 188 then (129, 60) else (122, 227))))) else (if i.val < 193 then (if i.val < 191 then (if i.val < 190 then (56, 230) else (96, 241)) else (if i.val < 192 then (125, 197) else (136, 181))) else (if i.val < 195 then (if i.val < 194 then (9, 68) else (53, 81)) else (if i.val < 196 then (7, 5) else (if i.val < 197 then (31, 202) else (131, 193)))))) else (if i.val < 207 then (if i.val < 202 then (if i.val < 200 then (if i.val < 199 then (141, 66) else (78, 69)) else (if i.val < 201 then (131, 249) else (74, 52))) else (if i.val < 204 then (if i.val < 203 then (111, 17) else (12, 179)) else (if i.val < 205 then (121, 47) else (if i.val < 206 then (28, 75) else (36, 205))))) else (if i.val < 211 then (if i.val < 209 then (if i.val < 208 then (70, 208) else (30, 26)) else (if i.val < 210 then (114, 171) else (83, 135))) else (if i.val < 213 then (if i.val < 212 then (137, 160) else (124, 126)) else (if i.val < 214 then (124, 226) else (if i.val < 215 then (114, 208) else (108, 105)))))))) else (if i.val < 252 then (if i.val < 234 then (if i.val < 225 then (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then (92, 99) else (142, 233)) else (if i.val < 219 then (131, 23) else (39, 95))) else (if i.val < 222 then (if i.val < 221 then (13, 142) else (53, 13)) else (if i.val < 223 then (131, 244) else (if i.val < 224 then (134, 172) else (131, 43))))) else (if i.val < 229 then (if i.val < 227 then (if i.val < 226 then (127, 34) else (131, 138)) else (if i.val < 228 then (112, 224) else (114, 71))) else (if i.val < 231 then (if i.val < 230 then (103, 113) else (121, 156)) else (if i.val < 232 then (105, 181) else (if i.val < 233 then (129, 206) else (52, 169)))))) else (if i.val < 243 then (if i.val < 238 then (if i.val < 236 then (if i.val < 235 then (88, 114) else (30, 19)) else (if i.val < 237 then (121, 112) else (59, 131))) else (if i.val < 240 then (if i.val < 239 then (105, 245) else (97, 131)) else (if i.val < 241 then (133, 238) else (if i.val < 242 then (143, 211) else (75, 84))))) else (if i.val < 247 then (if i.val < 245 then (if i.val < 244 then (114, 173) else (2, 174)) else (if i.val < 246 then (14, 229) else (16, 142))) else (if i.val < 249 then (if i.val < 248 then (112, 91) else (104, 175)) else (if i.val < 250 then (112, 185) else (if i.val < 251 then (91, 83) else (113, 39))))))) else (if i.val < 270 then (if i.val < 261 then (if i.val < 256 then (if i.val < 254 then (if i.val < 253 then (27, 73) else (120, 208)) else (if i.val < 255 then (37, 246) else (131, 28))) else (if i.val < 258 then (if i.val < 257 then (56, 2) else (89, 60)) else (if i.val < 259 then (79, 93) else (if i.val < 260 then (54, 148) else (11, 220))))) else (if i.val < 265 then (if i.val < 263 then (if i.val < 262 then (111, 212) else (58, 14)) else (if i.val < 264 then (30, 164) else (31, 199))) else (if i.val < 267 then (if i.val < 266 then (6, 32) else (84, 207)) else (if i.val < 268 then (57, 116) else (if i.val < 269 then (111, 120) else (62, 118)))))) else (if i.val < 279 then (if i.val < 274 then (if i.val < 272 then (if i.val < 271 then (115, 73) else (108, 237)) else (if i.val < 273 then (95, 157) else (101, 8))) else (if i.val < 276 then (if i.val < 275 then (40, 191) else (111, 209)) else (if i.val < 277 then (113, 98) else (if i.val < 278 then (99, 92) else (125, 229))))) else (if i.val < 283 then (if i.val < 281 then (if i.val < 280 then (56, 150) else (7, 139)) else (if i.val < 282 then (5, 147) else (141, 164))) else (if i.val < 285 then (if i.val < 284 then (112, 121) else (134, 162)) else (if i.val < 286 then (141, 175) else (if i.val < 287 then (89, 191) else (81, 207)))))))))) else (if i.val < 432 then (if i.val < 360 then (if i.val < 324 then (if i.val < 306 then (if i.val < 297 then (if i.val < 292 then (if i.val < 290 then (if i.val < 289 then (91, 1) else (134, 171)) else (if i.val < 291 then (117, 77) else (117, 98))) else (if i.val < 294 then (if i.val < 293 then (131, 48) else (109, 45)) else (if i.val < 295 then (85, 76) else (if i.val < 296 then (13, 127) else (88, 32))))) else (if i.val < 301 then (if i.val < 299 then (if i.val < 298 then (125, 5) else (97, 124)) else (if i.val < 300 then (139, 201) else (31, 196))) else (if i.val < 303 then (if i.val < 302 then (86, 61) else (26, 68)) else (if i.val < 304 then (112, 216) else (if i.val < 305 then (14, 120) else (1, 196)))))) else (if i.val < 315 then (if i.val < 310 then (if i.val < 308 then (if i.val < 307 then (81, 81) else (57, 0)) else (if i.val < 309 then (33, 224) else (105, 89))) else (if i.val < 312 then (if i.val < 311 then (128, 130) else (135, 140)) else (if i.val < 313 then (124, 132) else (if i.val < 314 then (121, 241) else (49, 55))))) else (if i.val < 319 then (if i.val < 317 then (if i.val < 316 then (91, 155) else (116, 57)) else (if i.val < 318 then (128, 137) else (15, 146))) else (if i.val < 321 then (if i.val < 320 then (31, 84) else (62, 209)) else (if i.val < 322 then (90, 244) else (if i.val < 323 then (130, 7) else (137, 16))))))) else (if i.val < 342 then (if i.val < 333 then (if i.val < 328 then (if i.val < 326 then (if i.val < 325 then (70, 203) else (48, 183)) else (if i.val < 327 then (86, 241) else (137, 32))) else (if i.val < 330 then (if i.val < 329 then (95, 169) else (70, 47)) else (if i.val < 331 then (88, 238) else (if i.val < 332 then (104, 66) else (86, 53))))) else (if i.val < 337 then (if i.val < 335 then (if i.val < 334 then (104, 29) else (118, 117)) else (if i.val < 336 then (58, 47) else (121, 48))) else (if i.val < 339 then (if i.val < 338 then (135, 86) else (44, 158)) else (if i.val < 340 then (93, 188) else (if i.val < 341 then (135, 178) else (87, 232)))))) else (if i.val < 351 then (if i.val < 346 then (if i.val < 344 then (if i.val < 343 then (22, 9) else (12, 182)) else (if i.val < 345 then (113, 113) else (16, 199))) else (if i.val < 348 then (if i.val < 347 then (131, 98) else (45, 220)) else (if i.val < 349 then (125, 26) else (if i.val < 350 then (57, 224) else (25, 23))))) else (if i.val < 355 then (if i.val < 353 then (if i.val < 352 then (57, 91) else (12, 123)) else (if i.val < 354 then (114, 39) else (66, 151))) else (if i.val < 357 then (if i.val < 356 then (32, 98) else (51, 206)) else (if i.val < 358 then (59, 5) else (if i.val < 359 then (113, 111) else (141, 202)))))))) else (if i.val < 396 then (if i.val < 378 then (if i.val < 369 then (if i.val < 364 then (if i.val < 362 then (if i.val < 361 then (100, 67) else (136, 32)) else (if i.val < 363 then (122, 47) else (87, 201))) else (if i.val < 366 then (if i.val < 365 then (113, 151) else (105, 204)) else (if i.val < 367 then (108, 244) else (if i.val < 368 then (89, 186) else (130, 55))))) else (if i.val < 373 then (if i.val < 371 then (if i.val < 370 then (47, 239) else (89, 185)) else (if i.val < 372 then (112, 69) else (130, 44))) else (if i.val < 375 then (if i.val < 374 then (109, 237) else (73, 30)) else (if i.val < 376 then (104, 228) else (if i.val < 377 then (47, 251) else (117, 211)))))) else (if i.val < 387 then (if i.val < 382 then (if i.val < 380 then (if i.val < 379 then (42, 219) else (46, 3)) else (if i.val < 381 then (64, 215) else (25, 78))) else (if i.val < 384 then (if i.val < 383 then (112, 209) else (79, 76)) else (if i.val < 385 then (11, 5) else (if i.val < 386 then (106, 212) else (78, 64))))) else (if i.val < 391 then (if i.val < 389 then (if i.val < 388 then (39, 168) else (86, 25)) else (if i.val < 390 then (40, 8) else (100, 3))) else (if i.val < 393 then (if i.val < 392 then (39, 96) else (75, 9)) else (if i.val < 394 then (118, 65) else (if i.val < 395 then (69, 142) else (143, 80))))))) else (if i.val < 414 then (if i.val < 405 then (if i.val < 400 then (if i.val < 398 then (if i.val < 397 then (88, 197) else (85, 100)) else (if i.val < 399 then (60, 81) else (131, 95))) else (if i.val < 402 then (if i.val < 401 then (26, 26) else (15, 122)) else (if i.val < 403 then (33, 220) else (if i.val < 404 then (100, 208) else (15, 197))))) else (if i.val < 409 then (if i.val < 407 then (if i.val < 406 then (46, 78) else (70, 50)) else (if i.val < 408 then (123, 77) else (2, 82))) else (if i.val < 411 then (if i.val < 410 then (60, 102) else (42, 0)) else (if i.val < 412 then (138, 164) else (if i.val < 413 then (14, 167) else (133, 61)))))) else (if i.val < 423 then (if i.val < 418 then (if i.val < 416 then (if i.val < 415 then (1, 150) else (67, 174)) else (if i.val < 417 then (0, 44) else (130, 19))) else (if i.val < 420 then (if i.val < 419 then (116, 161) else (131, 224)) else (if i.val < 421 then (109, 201) else (if i.val < 422 then (74, 30) else (91, 133))))) else (if i.val < 427 then (if i.val < 425 then (if i.val < 424 then (104, 232) else (62, 214)) else (if i.val < 426 then (134, 4) else (80, 173))) else (if i.val < 429 then (if i.val < 428 then (115, 101) else (31, 85)) else (if i.val < 430 then (65, 107) else (if i.val < 431 then (137, 66) else (44, 194))))))))) else (if i.val < 504 then (if i.val < 468 then (if i.val < 450 then (if i.val < 441 then (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then (56, 118) else (110, 23)) else (if i.val < 435 then (83, 60) else (131, 200))) else (if i.val < 438 then (if i.val < 437 then (83, 136) else (131, 190)) else (if i.val < 439 then (54, 171) else (if i.val < 440 then (97, 28) else (17, 185))))) else (if i.val < 445 then (if i.val < 443 then (if i.val < 442 then (127, 132) else (8, 16)) else (if i.val < 444 then (127, 53) else (125, 82))) else (if i.val < 447 then (if i.val < 446 then (128, 133) else (115, 64)) else (if i.val < 448 then (141, 85) else (if i.val < 449 then (116, 104) else (127, 189)))))) else (if i.val < 459 then (if i.val < 454 then (if i.val < 452 then (if i.val < 451 then (14, 172) else (86, 130)) else (if i.val < 453 then (23, 22) else (25, 180))) else (if i.val < 456 then (if i.val < 455 then (64, 122) else (11, 208)) else (if i.val < 457 then (14, 16) else (if i.val < 458 then (85, 86) else (52, 238))))) else (if i.val < 463 then (if i.val < 461 then (if i.val < 460 then (85, 120) else (103, 74)) else (if i.val < 462 then (17, 23) else (130, 65))) else (if i.val < 465 then (if i.val < 464 then (99, 105) else (117, 88)) else (if i.val < 466 then (128, 55) else (if i.val < 467 then (136, 78) else (94, 250))))))) else (if i.val < 486 then (if i.val < 477 then (if i.val < 472 then (if i.val < 470 then (if i.val < 469 then (136, 205) else (103, 72)) else (if i.val < 471 then (88, 71) else (103, 51))) else (if i.val < 474 then (if i.val < 473 then (110, 28) else (15, 50)) else (if i.val < 475 then (124, 16) else (if i.val < 476 then (115, 242) else (137, 225))))) else (if i.val < 481 then (if i.val < 479 then (if i.val < 478 then (92, 63) else (38, 214)) else (if i.val < 480 then (119, 228) else (90, 252))) else (if i.val < 483 then (if i.val < 482 then (86, 108) else (15, 20)) else (if i.val < 484 then (8, 214) else (if i.val < 485 then (6, 6) else (63, 145)))))) else (if i.val < 495 then (if i.val < 490 then (if i.val < 488 then (if i.val < 487 then (32, 135) else (128, 206)) else (if i.val < 489 then (38, 184) else (94, 182))) else (if i.val < 492 then (if i.val < 491 then (119, 186) else (140, 90)) else (if i.val < 493 then (65, 217) else (if i.val < 494 then (110, 249) else (42, 54))))) else (if i.val < 499 then (if i.val < 497 then (if i.val < 496 then (70, 42) else (83, 139)) else (if i.val < 498 then (131, 159) else (134, 178))) else (if i.val < 501 then (if i.val < 500 then (105, 82) else (116, 167)) else (if i.val < 502 then (33, 175) else (if i.val < 503 then (124, 21) else (55, 248)))))))) else (if i.val < 540 then (if i.val < 522 then (if i.val < 513 then (if i.val < 508 then (if i.val < 506 then (if i.val < 505 then (38, 50) else (96, 142)) else (if i.val < 507 then (122, 174) else (101, 201))) else (if i.val < 510 then (if i.val < 509 then (72, 20) else (127, 139)) else (if i.val < 511 then (97, 125) else (if i.val < 512 then (66, 142) else (71, 227))))) else (if i.val < 517 then (if i.val < 515 then (if i.val < 514 then (68, 189) else (135, 155)) else (if i.val < 516 then (103, 83) else (65, 232))) else (if i.val < 519 then (if i.val < 518 then (62, 11) else (77, 66)) else (if i.val < 520 then (42, 65) else (if i.val < 521 then (18, 125) else (103, 180)))))) else (if i.val < 531 then (if i.val < 526 then (if i.val < 524 then (if i.val < 523 then (118, 86) else (62, 237)) else (if i.val < 525 then (22, 81) else (32, 75))) else (if i.val < 528 then (if i.val < 527 then (115, 224) else (11, 21)) else (if i.val < 529 then (63, 225) else (if i.val < 530 then (92, 29) else (62, 183))))) else (if i.val < 535 then (if i.val < 533 then (if i.val < 532 then (111, 22) else (112, 29)) else (if i.val < 534 then (111, 254) else (59, 96))) else (if i.val < 537 then (if i.val < 536 then (56, 105) else (96, 141)) else (if i.val < 538 then (87, 7) else (if i.val < 539 then (132, 134) else (141, 197))))))) else (if i.val < 558 then (if i.val < 549 then (if i.val < 544 then (if i.val < 542 then (if i.val < 541 then (131, 110) else (41, 223)) else (if i.val < 543 then (102, 140) else (120, 223))) else (if i.val < 546 then (if i.val < 545 then (18, 252) else (111, 207)) else (if i.val < 547 then (33, 218) else (if i.val < 548 then (107, 66) else (16, 177))))) else (if i.val < 553 then (if i.val < 551 then (if i.val < 550 then (141, 203) else (47, 89)) else (if i.val < 552 then (10, 59) else (102, 109))) else (if i.val < 555 then (if i.val < 554 then (44, 9) else (77, 248)) else (if i.val < 556 then (72, 91) else (if i.val < 557 then (126, 146) else (121, 87)))))) else (if i.val < 567 then (if i.val < 562 then (if i.val < 560 then (if i.val < 559 then (41, 49) else (35, 152)) else (if i.val < 561 then (23, 131) else (111, 250))) else (if i.val < 564 then (if i.val < 563 then (86, 99) else (111, 88)) else (if i.val < 565 then (85, 169) else (if i.val < 566 then (118, 76) else (21, 198))))) else (if i.val < 571 then (if i.val < 569 then (if i.val < 568 then (122, 141) else (71, 136)) else (if i.val < 570 then (47, 23) else (111, 3))) else (if i.val < 573 then (if i.val < 572 then (111, 63) else (111, 16)) else (if i.val < 574 then (64, 168) else (if i.val < 575 then (111, 247) else (141, 86)))))))))))

def g32p_supplierGroup20_classify : Fin 576 → Fin 102 :=
  fun i => (if i.val < 288 then (if i.val < 144 then (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 90) else (if i.val < 3 then 83 else 94)) else (if i.val < 6 then (if i.val < 5 then 2 else 99) else (if i.val < 7 then 82 else (if i.val < 8 then 69 else 34)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 85 else 31) else (if i.val < 12 then 65 else 52)) else (if i.val < 15 then (if i.val < 14 then 72 else 52) else (if i.val < 16 then 52 else (if i.val < 17 then 18 else 63))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then 5 else 85) else (if i.val < 21 then 1 else 93)) else (if i.val < 24 then (if i.val < 23 then 5 else 90) else (if i.val < 25 then 52 else (if i.val < 26 then 79 else 82)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then 83 else 69) else (if i.val < 30 then 58 else 69)) else (if i.val < 33 then (if i.val < 32 then 69 else 31) else (if i.val < 34 then 55 else (if i.val < 35 then 34 else 79)))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then 76 else 51) else (if i.val < 39 then 94 else 31)) else (if i.val < 42 then (if i.val < 41 then 51 else 65) else (if i.val < 43 then 31 else (if i.val < 44 then 83 else 7)))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then 83 else 58) else (if i.val < 48 then 17 else 7)) else (if i.val < 51 then (if i.val < 50 then 7 else 83) else (if i.val < 52 then 94 else (if i.val < 53 then 89 else 18))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then 55 else 80) else (if i.val < 57 then 58 else 76)) else (if i.val < 60 then (if i.val < 59 then 51 else 76) else (if i.val < 61 then 98 else (if i.val < 62 then 101 else 13)))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then 69 else 2) else (if i.val < 66 then 94 else 31)) else (if i.val < 69 then (if i.val < 68 then 55 else 31) else (if i.val < 70 then 31 else (if i.val < 71 then 97 else 7))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 83 else 2) else (if i.val < 75 then 64 else 23)) else (if i.val < 78 then (if i.val < 77 then 34 else 13) else (if i.val < 79 then 95 else (if i.val < 80 then 52 else 13)))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then 69 else 63) else (if i.val < 84 then 69 else 55)) else (if i.val < 87 then (if i.val < 86 then 80 else 63) else (if i.val < 88 then 63 else (if i.val < 89 then 69 else 34))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then 28 else 90) else (if i.val < 93 then 7 else 41)) else (if i.val < 96 then (if i.val < 95 then 27 else 87) else (if i.val < 97 then 23 else (if i.val < 98 then 64 else 44)))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then 96 else 5) else (if i.val < 102 then 63 else 5)) else (if i.val < 105 then (if i.val < 104 then 5 else 27) else (if i.val < 106 then 90 else (if i.val < 107 then 95 else 19)))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 85 else 27) else (if i.val < 111 then 90 else 72)) else (if i.val < 114 then (if i.val < 113 then 52 else 63) else (if i.val < 115 then 61 else (if i.val < 116 then 72 else 80)))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 63 else 80) else (if i.val < 120 then 61 else 63)) else (if i.val < 123 then (if i.val < 122 then 61 else 72) else (if i.val < 124 then 63 else (if i.val < 125 then 5 else 28))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then 81 else 3) else (if i.val < 129 then 41 else 27)) else (if i.val < 132 then (if i.val < 131 then 41 else 48) else (if i.val < 133 then 87 else (if i.val < 134 then 90 else 44)))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then 90 else 44) else (if i.val < 138 then 52 else 94)) else (if i.val < 141 then (if i.val < 140 then 100 else 37) else (if i.val < 142 then 13 else (if i.val < 143 then 72 else 13)))))))) else (if i.val < 216 then (if i.val < 180 then (if i.val < 162 then (if i.val < 153 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 13 else 94) else (if i.val < 147 then 63 else 69)) else (if i.val < 150 then (if i.val < 149 then 100 else 8) else (if i.val < 151 then 93 else (if i.val < 152 then 90 else 27)))) else (if i.val < 157 then (if i.val < 155 then (if i.val < 154 then 90 else 72) else (if i.val < 156 then 20 else 27)) else (if i.val < 159 then (if i.val < 158 then 27 else 90) else (if i.val < 160 then 52 else (if i.val < 161 then 95 else 63))))) else (if i.val < 171 then (if i.val < 166 then (if i.val < 164 then (if i.val < 163 then 61 else 72) else (if i.val < 165 then 8 else 93)) else (if i.val < 168 then (if i.val < 167 then 8 else 91) else (if i.val < 169 then 5 else (if i.val < 170 then 34 else 55)))) else (if i.val < 175 then (if i.val < 173 then (if i.val < 172 then 34 else 34) else (if i.val < 174 then 7 else 13)) else (if i.val < 177 then (if i.val < 176 then 93 else 91) else (if i.val < 178 then 67 else (if i.val < 179 then 7 else 13)))))) else (if i.val < 198 then (if i.val < 189 then (if i.val < 184 then (if i.val < 182 then (if i.val < 181 then 58 else 69) else (if i.val < 183 then 27 else 48)) else (if i.val < 186 then (if i.val < 185 then 58 else 41) else (if i.val < 187 then 27 else (if i.val < 188 then 20 else 48)))) else (if i.val < 193 then (if i.val < 191 then (if i.val < 190 then 27 else 48) else (if i.val < 192 then 58 else 55)) else (if i.val < 195 then (if i.val < 194 then 34 else 95) else (if i.val < 196 then 19 else (if i.val < 197 then 100 else 17))))) else (if i.val < 207 then (if i.val < 202 then (if i.val < 200 then (if i.val < 199 then 72 else 61) else (if i.val < 201 then 20 else 8)) else (if i.val < 204 then (if i.val < 203 then 52 else 88) else (if i.val < 205 then 52 else (if i.val < 206 then 91 else 31)))) else (if i.val < 211 then (if i.val < 209 then (if i.val < 208 then 83 else 67) else (if i.val < 210 then 58 else 94)) else (if i.val < 213 then (if i.val < 212 then 55 else 80) else (if i.val < 214 then 58 else (if i.val < 215 then 58 else 94))))))) else (if i.val < 252 then (if i.val < 234 then (if i.val < 225 then (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 7 else 41) else (if i.val < 219 then 55 else 67)) else (if i.val < 222 then (if i.val < 221 then 91 else 77) else (if i.val < 223 then 7 else (if i.val < 224 then 41 else 55)))) else (if i.val < 229 then (if i.val < 227 then (if i.val < 226 then 58 else 17) else (if i.val < 228 then 7 else 48)) else (if i.val < 231 then (if i.val < 230 then 58 else 48) else (if i.val < 232 then 17 else (if i.val < 233 then 41 else 69))))) else (if i.val < 243 then (if i.val < 238 then (if i.val < 236 then (if i.val < 235 then 48 else 69) else (if i.val < 237 then 48 else 48)) else (if i.val < 240 then (if i.val < 239 then 58 else 48) else (if i.val < 241 then 17 else (if i.val < 242 then 55 else 80)))) else (if i.val < 247 then (if i.val < 245 then (if i.val < 244 then 58 else 19) else (if i.val < 246 then 100 else 19)) else (if i.val < 249 then (if i.val < 248 then 17 else 34) else (if i.val < 250 then 20 else (if i.val < 251 then 34 else 20)))))) else (if i.val < 270 then (if i.val < 261 then (if i.val < 256 then (if i.val < 254 then (if i.val < 253 then 88 else 52) else (if i.val < 255 then 31 else 52)) else (if i.val < 258 then (if i.val < 257 then 85 else 31) else (if i.val < 259 then 34 else (if i.val < 260 then 79 else 83)))) else (if i.val < 265 then (if i.val < 263 then (if i.val < 262 then 63 else 5) else (if i.val < 264 then 79 else 76)) else (if i.val < 267 then (if i.val < 266 then 28 else 13) else (if i.val < 268 then 7 else (if i.val < 269 then 13 else 63))))) else (if i.val < 279 then (if i.val < 274 then (if i.val < 272 then (if i.val < 271 then 61 else 7) else (if i.val < 273 then 7 else 13)) else (if i.val < 276 then (if i.val < 275 then 69 else 89) else (if i.val < 277 then 27 else (if i.val < 278 then 48 else 58)))) else (if i.val < 283 then (if i.val < 281 then (if i.val < 280 then 77 else 28) else (if i.val < 282 then 81 else 55)) else (if i.val < 285 then (if i.val < 284 then 7 else 41) else (if i.val < 286 then 55 else (if i.val < 287 then 61 else 7))))))))) else (if i.val < 432 then (if i.val < 360 then (if i.val < 324 then (if i.val < 306 then (if i.val < 297 then (if i.val < 292 then (if i.val < 290 then (if i.val < 289 then 61 else 41) else (if i.val < 291 then 7 else 41)) else (if i.val < 294 then (if i.val < 293 then 55 else 7) else (if i.val < 295 then 89 else (if i.val < 296 then 88 else 48)))) else (if i.val < 301 then (if i.val < 299 then (if i.val < 298 then 58 else 48) else (if i.val < 300 then 17 else 77)) else (if i.val < 303 then (if i.val < 302 then 5 else 81) else (if i.val < 304 then 5 else (if i.val < 305 then 81 else 13))))) else (if i.val < 315 then (if i.val < 310 then (if i.val < 308 then (if i.val < 307 then 69 else 3) else (if i.val < 309 then 27 else 34)) else (if i.val < 312 then (if i.val < 311 then 7 else 41) else (if i.val < 313 then 27 else (if i.val < 314 then 27 else 34)))) else (if i.val < 319 then (if i.val < 317 then (if i.val < 316 then 58 else 17) else (if i.val < 318 then 72 else 2)) else (if i.val < 321 then (if i.val < 320 then 98 else 64) else (if i.val < 322 then 58 else (if i.val < 323 then 72 else 55)))))) else (if i.val < 342 then (if i.val < 333 then (if i.val < 328 then (if i.val < 326 then (if i.val < 325 then 80 else 63) else (if i.val < 327 then 20 else 55)) else (if i.val < 330 then (if i.val < 329 then 41 else 80) else (if i.val < 331 then 61 else (if i.val < 332 then 34 else 20)))) else (if i.val < 337 then (if i.val < 335 then (if i.val < 334 then 34 else 41) else (if i.val < 336 then 20 else 55)) else (if i.val < 339 then (if i.val < 338 then 41 else 80) else (if i.val < 340 then 7 else (if i.val < 341 then 41 else 27))))) else (if i.val < 351 then (if i.val < 346 then (if i.val < 344 then (if i.val < 343 then 67 else 88) else (if i.val < 345 then 48 else 13)) else (if i.val < 348 then (if i.val < 347 then 61 else 13) else (if i.val < 349 then 17 else (if i.val < 350 then 5 else 83)))) else (if i.val < 355 then (if i.val < 353 then (if i.val < 352 then 5 else 83) else (if i.val < 354 then 27 else 72)) else (if i.val < 357 then (if i.val < 356 then 3 else 87) else (if i.val < 358 then 27 else (if i.val < 359 then 48 else 63))))))) else (if i.val < 396 then (if i.val < 378 then (if i.val < 369 then (if i.val < 364 then (if i.val < 362 then (if i.val < 361 then 27 else 41) else (if i.val < 363 then 48 else 27)) else (if i.val < 366 then (if i.val < 365 then 48 else 63) else (if i.val < 367 then 72 else (if i.val < 368 then 17 else 20)))) else (if i.val < 373 then (if i.val < 371 then (if i.val < 370 then 83 else 64) else (if i.val < 372 then 17 else 72)) else (if i.val < 375 then (if i.val < 374 then 20 else 80) else (if i.val < 376 then 63 else (if i.val < 377 then 80 else 20))))) else (if i.val < 387 then (if i.val < 382 then (if i.val < 380 then (if i.val < 379 then 69 else 80) else (if i.val < 381 then 69 else 80)) else (if i.val < 384 then (if i.val < 383 then 20 else 34) else (if i.val < 385 then 69 else (if i.val < 386 then 34 else 58)))) else (if i.val < 391 then (if i.val < 389 then (if i.val < 388 then 69 else 20) else (if i.val < 390 then 69 else 80)) else (if i.val < 393 then (if i.val < 392 then 69 else 80) else (if i.val < 394 then 41 else (if i.val < 395 then 27 else 41)))))) else (if i.val < 414 then (if i.val < 405 then (if i.val < 400 then (if i.val < 398 then (if i.val < 397 then 31 else 77) else (if i.val < 399 then 31 else 61)) else (if i.val < 402 then (if i.val < 401 then 13 else 34) else (if i.val < 403 then 13 else (if i.val < 404 then 55 else 34)))) else (if i.val < 409 then (if i.val < 407 then (if i.val < 406 then 83 else 51) else (if i.val < 408 then 55 else 34)) else (if i.val < 411 then (if i.val < 410 then 3 else 23) else (if i.val < 412 then 55 else (if i.val < 413 then 80 else 58))))) else (if i.val < 423 then (if i.val < 418 then (if i.val < 416 then (if i.val < 415 then 87 else 23) else (if i.val < 417 then 44 else 72)) else (if i.val < 420 then (if i.val < 419 then 58 else 17) else (if i.val < 421 then 72 else (if i.val < 422 then 48 else 58)))) else (if i.val < 427 then (if i.val < 425 then (if i.val < 424 then 17 else 58) else (if i.val < 426 then 17 else 72)) else (if i.val < 429 then (if i.val < 428 then 63 else 98) else (if i.val < 430 then 20 else (if i.val < 431 then 55 else 80)))))))) else (if i.val < 504 then (if i.val < 468 then (if i.val < 450 then (if i.val < 441 then (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then 90 else 72) else (if i.val < 435 then 20 else 17)) else (if i.val < 438 then (if i.val < 437 then 72 else 17) else (if i.val < 439 then 20 else (if i.val < 440 then 48 else 13)))) else (if i.val < 445 then (if i.val < 443 then (if i.val < 442 then 17 else 13) else (if i.val < 444 then 17 else 17)) else (if i.val < 447 then (if i.val < 446 then 72 else 17) else (if i.val < 448 then 20 else (if i.val < 449 then 63 else 61))))) else (if i.val < 459 then (if i.val < 454 then (if i.val < 452 then (if i.val < 451 then 98 else 20) else (if i.val < 453 then 69 else 80)) else (if i.val < 456 then (if i.val < 455 then 69 else 80) else (if i.val < 457 then 94 else (if i.val < 458 then 90 else 94)))) else (if i.val < 463 then (if i.val < 461 then (if i.val < 460 then 7 else 58) else (if i.val < 462 then 1 else 72)) else (if i.val < 465 then (if i.val < 464 then 55 else 72) else (if i.val < 466 then 61 else (if i.val < 467 then 20 else 72)))))) else (if i.val < 486 then (if i.val < 477 then (if i.val < 472 then (if i.val < 470 then (if i.val < 469 then 55 else 63) else (if i.val < 471 then 48 else 61)) else (if i.val < 474 then (if i.val < 473 then 94 else 1) else (if i.val < 475 then 80 else (if i.val < 476 then 63 else 27)))) else (if i.val < 481 then (if i.val < 479 then (if i.val < 478 then 20 else 34) else (if i.val < 480 then 41 else 34)) else (if i.val < 483 then (if i.val < 482 then 20 else 13) else (if i.val < 484 then 34 else (if i.val < 485 then 13 else 34))))) else (if i.val < 495 then (if i.val < 490 then (if i.val < 488 then (if i.val < 487 then 34 else 41) else (if i.val < 489 then 34 else 20)) else (if i.val < 492 then (if i.val < 491 then 72 else 61) else (if i.val < 493 then 69 else (if i.val < 494 then 13 else 69)))) else (if i.val < 499 then (if i.val < 497 then (if i.val < 496 then 13 else 94) else (if i.val < 498 then 7 else 41)) else (if i.val < 501 then (if i.val < 500 then 58 else 17) else (if i.val < 502 then 1 else (if i.val < 503 then 55 else 80))))))) else (if i.val < 540 then (if i.val < 522 then (if i.val < 513 then (if i.val < 508 then (if i.val < 506 then (if i.val < 505 then 34 else 20) else (if i.val < 507 then 55 else 80)) else (if i.val < 510 then (if i.val < 509 then 13 else 61) else (if i.val < 511 then 80 else (if i.val < 512 then 69 else 48)))) else (if i.val < 517 then (if i.val < 515 then (if i.val < 514 then 69 else 41) else (if i.val < 516 then 34 else 69)) else (if i.val < 519 then (if i.val < 518 then 34 else 63) else (if i.val < 520 then 69 else (if i.val < 521 then 34 else 63))))) else (if i.val < 531 then (if i.val < 526 then (if i.val < 524 then (if i.val < 523 then 41 else 34) else (if i.val < 525 then 69 else 34)) else (if i.val < 528 then (if i.val < 527 then 63 else 69) else (if i.val < 529 then 34 else (if i.val < 530 then 20 else 34)))) else (if i.val < 535 then (if i.val < 533 then (if i.val < 532 then 13 else 27) else (if i.val < 534 then 7 else 27)) else (if i.val < 537 then (if i.val < 536 then 89 else 41) else (if i.val < 538 then 27 else (if i.val < 539 then 48 else 61)))))) else (if i.val < 558 then (if i.val < 549 then (if i.val < 544 then (if i.val < 542 then (if i.val < 541 then 61 else 69) else (if i.val < 543 then 61 else 48)) else (if i.val < 546 then (if i.val < 545 then 34 else 61) else (if i.val < 547 then 13 else (if i.val < 548 then 61 else 13)))) else (if i.val < 553 then (if i.val < 551 then (if i.val < 550 then 61 else 13) else (if i.val < 552 then 69 else 13)) else (if i.val < 555 then (if i.val < 554 then 13 else 61) else (if i.val < 556 then 13 else (if i.val < 557 then 61 else 48))))) else (if i.val < 567 then (if i.val < 562 then (if i.val < 560 then (if i.val < 559 then 69 else 34) else (if i.val < 561 then 69 else 17)) else (if i.val < 564 then (if i.val < 563 then 7 else 13) else (if i.val < 565 then 17 else (if i.val < 566 then 7 else 69)))) else (if i.val < 571 then (if i.val < 569 then (if i.val < 568 then 80 else 13) else (if i.val < 570 then 13 else 13)) else (if i.val < 573 then (if i.val < 572 then 13 else 13) else (if i.val < 574 then 69 else (if i.val < 575 then 17 else 72))))))))))

def g32p_supplierGroup20_support : Finset (Fin 102) :=
  {0, 1, 2, 3, 5, 7, 8, 13, 17, 18, 19, 20, 23, 27, 28, 31, 34, 37, 41, 44, 48, 51, 52, 55, 58, 61, 63, 64, 65, 67, 69, 72, 76, 77, 79, 80, 81, 82, 83, 85, 87, 88, 89, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup20_matrix_000 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 0 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 0 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 0 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 0 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 0 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_001 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 1 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 1 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 1 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 1 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 1 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_002 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 2 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 2 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 2 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 2 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 2 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_003 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 3 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 3 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 3 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 3 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 3 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_004 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 4 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 4 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 4 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 4 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 4 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_005 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 5 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 5 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 5 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 5 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 5 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_006 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 6 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 6 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 6 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 6 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 6 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_007 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 7 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 7 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 7 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 7 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 7 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_008 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 8 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 8 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 8 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 8 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 8 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_009 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 9 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 9 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 9 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 9 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 9 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_010 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 10 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 10 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 10 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 10 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 10 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_011 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 11 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 11 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 11 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 11 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 11 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_012 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 12 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 12 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 12 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 12 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 12 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_013 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 13 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 13 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 13 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 13 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 13 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_014 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 14 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 14 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 14 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 14 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 14 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_015 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 15 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 15 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 15 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 15 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 15 r) ∈ g32p_supplierGroup20_support := by
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

theorem g32p_supplierGroup20_matrix_016 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 16 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 16 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 16 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 16 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 16 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_017 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 17 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 17 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 17 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 17 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 17 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_018 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 18 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 18 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 18 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 18 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 18 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_019 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 19 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 19 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 19 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 19 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 19 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_020 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 20 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 20 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 20 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 20 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 20 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_021 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 21 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 21 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 21 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 21 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 21 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_022 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 22 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 22 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 22 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 22 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 22 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_023 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 23 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 23 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 23 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 23 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 23 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_024 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 24 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 24 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 24 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_024 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 24 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 24 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 24 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_024 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 24 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_025 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 25 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 25 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 25 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_025 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 25 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 25 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 25 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_025 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 25 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_026 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 26 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 26 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 26 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_026 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 26 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 26 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 26 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_026 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 26 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_027 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 27 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 27 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 27 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_027 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 27 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 27 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 27 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_027 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 27 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_028 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 28 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 28 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 28 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_028 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 28 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 28 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 28 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_028 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 28 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_029 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 29 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 29 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 29 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_029 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 29 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 29 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 29 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_029 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 29 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_030 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 30 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 30 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 30 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_030 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 30 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 30 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 30 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_030 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 30 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_031 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 31 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 31 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 31 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_031 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 31 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 31 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 31 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_031 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 31 r) ∈ g32p_supplierGroup20_support := by
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

theorem g32p_supplierGroup20_matrix_032 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 32 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 32 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 32 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_032 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 32 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 32 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 32 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_032 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 32 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_033 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 33 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 33 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 33 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_033 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 33 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 33 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 33 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_033 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 33 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_034 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 34 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 34 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 34 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_034 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 34 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 34 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 34 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_034 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 34 r) ∈ g32p_supplierGroup20_support := by
  decide +kernel

theorem g32p_supplierGroup20_matrix_035 : ∀ r : Fin 16,
    g32p_row26_groupNodes (g32p_finBlockIndex 576 35 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 35 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 35 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup20_class_035 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup20_source (g32p_finBlockIndex 576 35 r)).1 (g32p_supplierGroup20_source (g32p_finBlockIndex 576 35 r)).2 =
      g32p_supplierGroup20_classify (g32p_finBlockIndex 576 35 r) := by
  decide +kernel

theorem g32p_supplierGroup20_support_035 : ∀ r : Fin 16,
    g32p_supplierGroup20_classify (g32p_finBlockIndex 576 35 r) ∈ g32p_supplierGroup20_support := by
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

theorem g32p_supplierGroup20_matrix (i : Fin 576) :
    g32p_row26_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source i).1 (g32p_supplierGroup20_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row26_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup20_source i).1 (g32p_supplierGroup20_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup20_matrix_000 r
  · exact g32p_supplierGroup20_matrix_001 r
  · exact g32p_supplierGroup20_matrix_002 r
  · exact g32p_supplierGroup20_matrix_003 r
  · exact g32p_supplierGroup20_matrix_004 r
  · exact g32p_supplierGroup20_matrix_005 r
  · exact g32p_supplierGroup20_matrix_006 r
  · exact g32p_supplierGroup20_matrix_007 r
  · exact g32p_supplierGroup20_matrix_008 r
  · exact g32p_supplierGroup20_matrix_009 r
  · exact g32p_supplierGroup20_matrix_010 r
  · exact g32p_supplierGroup20_matrix_011 r
  · exact g32p_supplierGroup20_matrix_012 r
  · exact g32p_supplierGroup20_matrix_013 r
  · exact g32p_supplierGroup20_matrix_014 r
  · exact g32p_supplierGroup20_matrix_015 r
  · exact g32p_supplierGroup20_matrix_016 r
  · exact g32p_supplierGroup20_matrix_017 r
  · exact g32p_supplierGroup20_matrix_018 r
  · exact g32p_supplierGroup20_matrix_019 r
  · exact g32p_supplierGroup20_matrix_020 r
  · exact g32p_supplierGroup20_matrix_021 r
  · exact g32p_supplierGroup20_matrix_022 r
  · exact g32p_supplierGroup20_matrix_023 r
  · exact g32p_supplierGroup20_matrix_024 r
  · exact g32p_supplierGroup20_matrix_025 r
  · exact g32p_supplierGroup20_matrix_026 r
  · exact g32p_supplierGroup20_matrix_027 r
  · exact g32p_supplierGroup20_matrix_028 r
  · exact g32p_supplierGroup20_matrix_029 r
  · exact g32p_supplierGroup20_matrix_030 r
  · exact g32p_supplierGroup20_matrix_031 r
  · exact g32p_supplierGroup20_matrix_032 r
  · exact g32p_supplierGroup20_matrix_033 r
  · exact g32p_supplierGroup20_matrix_034 r
  · exact g32p_supplierGroup20_matrix_035 r

theorem g32p_supplierGroup20_class (i : Fin 576) :
    g32p_supplierForest_classes (g32p_supplierGroup20_source i).1 (g32p_supplierGroup20_source i).2 =
      g32p_supplierGroup20_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup20_source i).1 (g32p_supplierGroup20_source i).2 =
      g32p_supplierGroup20_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup20_class_000 r
  · exact g32p_supplierGroup20_class_001 r
  · exact g32p_supplierGroup20_class_002 r
  · exact g32p_supplierGroup20_class_003 r
  · exact g32p_supplierGroup20_class_004 r
  · exact g32p_supplierGroup20_class_005 r
  · exact g32p_supplierGroup20_class_006 r
  · exact g32p_supplierGroup20_class_007 r
  · exact g32p_supplierGroup20_class_008 r
  · exact g32p_supplierGroup20_class_009 r
  · exact g32p_supplierGroup20_class_010 r
  · exact g32p_supplierGroup20_class_011 r
  · exact g32p_supplierGroup20_class_012 r
  · exact g32p_supplierGroup20_class_013 r
  · exact g32p_supplierGroup20_class_014 r
  · exact g32p_supplierGroup20_class_015 r
  · exact g32p_supplierGroup20_class_016 r
  · exact g32p_supplierGroup20_class_017 r
  · exact g32p_supplierGroup20_class_018 r
  · exact g32p_supplierGroup20_class_019 r
  · exact g32p_supplierGroup20_class_020 r
  · exact g32p_supplierGroup20_class_021 r
  · exact g32p_supplierGroup20_class_022 r
  · exact g32p_supplierGroup20_class_023 r
  · exact g32p_supplierGroup20_class_024 r
  · exact g32p_supplierGroup20_class_025 r
  · exact g32p_supplierGroup20_class_026 r
  · exact g32p_supplierGroup20_class_027 r
  · exact g32p_supplierGroup20_class_028 r
  · exact g32p_supplierGroup20_class_029 r
  · exact g32p_supplierGroup20_class_030 r
  · exact g32p_supplierGroup20_class_031 r
  · exact g32p_supplierGroup20_class_032 r
  · exact g32p_supplierGroup20_class_033 r
  · exact g32p_supplierGroup20_class_034 r
  · exact g32p_supplierGroup20_class_035 r

theorem g32p_supplierGroup20_support_mem (i : Fin 576) :
    g32p_supplierGroup20_classify i ∈ g32p_supplierGroup20_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup20_classify i ∈ g32p_supplierGroup20_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup20_support_000 r
  · exact g32p_supplierGroup20_support_001 r
  · exact g32p_supplierGroup20_support_002 r
  · exact g32p_supplierGroup20_support_003 r
  · exact g32p_supplierGroup20_support_004 r
  · exact g32p_supplierGroup20_support_005 r
  · exact g32p_supplierGroup20_support_006 r
  · exact g32p_supplierGroup20_support_007 r
  · exact g32p_supplierGroup20_support_008 r
  · exact g32p_supplierGroup20_support_009 r
  · exact g32p_supplierGroup20_support_010 r
  · exact g32p_supplierGroup20_support_011 r
  · exact g32p_supplierGroup20_support_012 r
  · exact g32p_supplierGroup20_support_013 r
  · exact g32p_supplierGroup20_support_014 r
  · exact g32p_supplierGroup20_support_015 r
  · exact g32p_supplierGroup20_support_016 r
  · exact g32p_supplierGroup20_support_017 r
  · exact g32p_supplierGroup20_support_018 r
  · exact g32p_supplierGroup20_support_019 r
  · exact g32p_supplierGroup20_support_020 r
  · exact g32p_supplierGroup20_support_021 r
  · exact g32p_supplierGroup20_support_022 r
  · exact g32p_supplierGroup20_support_023 r
  · exact g32p_supplierGroup20_support_024 r
  · exact g32p_supplierGroup20_support_025 r
  · exact g32p_supplierGroup20_support_026 r
  · exact g32p_supplierGroup20_support_027 r
  · exact g32p_supplierGroup20_support_028 r
  · exact g32p_supplierGroup20_support_029 r
  · exact g32p_supplierGroup20_support_030 r
  · exact g32p_supplierGroup20_support_031 r
  · exact g32p_supplierGroup20_support_032 r
  · exact g32p_supplierGroup20_support_033 r
  · exact g32p_supplierGroup20_support_034 r
  · exact g32p_supplierGroup20_support_035 r

end HodgeLean.Foundations.Program

end
end
