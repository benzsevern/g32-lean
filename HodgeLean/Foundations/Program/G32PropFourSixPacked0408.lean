import HodgeLean.Foundations.Program.G32PropFourSixPacked0407
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow30
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

theorem g32p_row29_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 100 = [3, 1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_100 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 100) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 100) (g32p_literalTraceValue 28 100)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_100]
  decide +kernel

theorem g32p_row29_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 101 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 101) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 101) (g32p_literalTraceValue 28 101)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row29_traceCoefficients_101]
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

def g32p_row29_generatorIndex : Fin 8 → Fin 408 :=
  ![28, 79, 130, 181, 260, 261, 362, 363]

theorem g32p_row29_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup07_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 28 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 28 g32p_row29_supplierClass
    g32p_row29_supplierClass_isConj g32p_supplierGroup07_support g32p_row29_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row29_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup07_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row29_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 28 c false (g32p_row29_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 28 c true (g32p_row29_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 28 c false (g32p_row29_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 28 c true (g32p_row29_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 28 c false (g32p_row29_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 28 c false (g32p_row29_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 28 c true (g32p_row29_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 28 c true (g32p_row29_coinduced_zero c hc true) 3

theorem g32p_row29_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row29_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row29_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row29_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row29_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row29_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row29_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row29_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row29_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row29_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row29_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row29_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row29_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row29_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row29_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup07_support) :
    g32p_literalTraceValue (g32p_row29_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup07_support →
    g32p_literalTraceValue (g32p_row29_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row29_zeroTrace_block_00 r k
  · exact g32p_row29_zeroTrace_block_01 r k
  · exact g32p_row29_zeroTrace_block_02 r k
  · exact g32p_row29_zeroTrace_block_03 r k
  · exact g32p_row29_zeroTrace_block_04 r k
  · exact g32p_row29_zeroTrace_block_05 r k
  · exact g32p_row29_zeroTrace_block_06 r k

theorem g32p_row29_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup07_support) :
    (g32p_recordedInductionGenerators (g32p_row29_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row29_generatorIndex k) c) := by
  rw [g32p_row29_recordedGenerator_zero c hc k, g32p_row29_zeroTrace_arithmetic c k hc]
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

def g32p_row29_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [11664] else [3888])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [3888] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [1944])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [486] else (if i.val < 14 then [] else [486])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else [1944]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [1944] else [486])) else (if i.val < 36 then (if i.val < 35 then [] else [1944]) else (if i.val < 37 then [486] else [155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [486] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [486] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [3888] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [486] else (if i.val < 56 then [] else [1944]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [486])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [11664] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else [3888]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [1944])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [3888])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [3888] else [3888])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [3888] else []))) else (if i.val < 98 then (if i.val < 96 then [11664] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [11664] else []) else (if i.val < 101 then [] else [155520])))))))

theorem g32p_row29_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup07_support) :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) c) (g32p_literalTraceValue 28 c)
      [1, 1, 1] (g32p_row29_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row29_tracePolynomial_000
  · exact g32p_row29_tracePolynomial_001
  · exact g32p_row29_tracePolynomial_002
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_009
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_011
  · exact g32p_row29_tracePolynomial_012
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_014
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (18 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_032
  · exact g32p_row29_tracePolynomial_033
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_035
  · exact g32p_row29_tracePolynomial_036
  · exact g32p_row29_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_039
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_042
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_044
  · exact g32p_row29_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_053
  · exact g32p_row29_tracePolynomial_054
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_062
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_067
  · exact g32p_row29_tracePolynomial_068
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_070
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_075
  · exact g32p_row29_tracePolynomial_076
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_087
  · exact g32p_row29_tracePolynomial_088
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_092
  · exact g32p_row29_tracePolynomial_093
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row29_tracePolynomial_095
  · exact g32p_row29_tracePolynomial_096
  · exact g32p_row29_tracePolynomial_097
  · exact g32p_row29_tracePolynomial_098
  · exact g32p_row29_tracePolynomial_099
  · exact g32p_row29_tracePolynomial_100
  · exact g32p_row29_tracePolynomial_101

theorem g32p_row29_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 28 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 28 c) := by
  by_cases hc : c ∈ g32p_supplierGroup07_support
  · have hclass (j : Fin 486) :
        IsConj (g32p_literalRepresentative c) (g32p_row09_groupEquiv j : g32p_G) ↔
          g32p_row29_supplierClassifier j = c := by
      simpa only [g32p_row29_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row29_supplierClass_iff (g32p_row09_groupEquiv j) c
    have hχ (j : Fin 486) :
        (g32p_recordedSupplierCharacters 28 (g32p_row09_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row29_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 28 (show (g32p_recordedSuppliers 28).H from g32p_row09_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row29_characterValues (g32p_row09_groupEquiv.symm (g32p_row09_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 28).H (g32p_recordedSupplierCharacters 28)
      (g32p_literalRepresentative c) g32p_row09_groupEquiv g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) c 3 486
      (g32p_literalCentralizer c) (g32p_literalTraceValue 28 c) [1, 1, 1]
      (g32p_row29_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row29_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 28)))
      (g32p_row29_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row29_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row29_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
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

theorem g32p_row29_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
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

theorem g32p_row29_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
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

theorem g32p_row29_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
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

theorem g32p_row29_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
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

theorem g32p_row29_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
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

theorem g32p_row29_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row29_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row29_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
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

theorem g32p_row29_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row29_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row29_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row29_variantArithmetic_00_0 r
  · exact g32p_row29_variantArithmetic_01_0 r
  · exact g32p_row29_variantArithmetic_02_0 r
  · exact g32p_row29_variantArithmetic_03_0 r
  · exact g32p_row29_variantArithmetic_04_0 r
  · exact g32p_row29_variantArithmetic_05_0 r
  · exact g32p_row29_variantArithmetic_06_0 r

theorem g32p_row29_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row29_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row29_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row29_variantArithmetic_00_1 r
  · exact g32p_row29_variantArithmetic_01_1 r
  · exact g32p_row29_variantArithmetic_02_1 r
  · exact g32p_row29_variantArithmetic_03_1 r
  · exact g32p_row29_variantArithmetic_04_1 r
  · exact g32p_row29_variantArithmetic_05_1 r
  · exact g32p_row29_variantArithmetic_06_1 r

theorem g32p_row29_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row29_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row29_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row29_variantArithmetic_00_2 r
  · exact g32p_row29_variantArithmetic_01_2 r
  · exact g32p_row29_variantArithmetic_02_2 r
  · exact g32p_row29_variantArithmetic_03_2 r
  · exact g32p_row29_variantArithmetic_04_2 r
  · exact g32p_row29_variantArithmetic_05_2 r
  · exact g32p_row29_variantArithmetic_06_2 r

theorem g32p_row29_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row29_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row29_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row29_variantArithmetic_00_3 r
  · exact g32p_row29_variantArithmetic_01_3 r
  · exact g32p_row29_variantArithmetic_02_3 r
  · exact g32p_row29_variantArithmetic_03_3 r
  · exact g32p_row29_variantArithmetic_04_3 r
  · exact g32p_row29_variantArithmetic_05_3 r
  · exact g32p_row29_variantArithmetic_06_3 r

theorem g32p_row29_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row29_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row29_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row29_variantArithmetic_00_4 r
  · exact g32p_row29_variantArithmetic_01_4 r
  · exact g32p_row29_variantArithmetic_02_4 r
  · exact g32p_row29_variantArithmetic_03_4 r
  · exact g32p_row29_variantArithmetic_04_4 r
  · exact g32p_row29_variantArithmetic_05_4 r
  · exact g32p_row29_variantArithmetic_06_4 r

theorem g32p_row29_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row29_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row29_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row29_variantArithmetic_00_5 r
  · exact g32p_row29_variantArithmetic_01_5 r
  · exact g32p_row29_variantArithmetic_02_5 r
  · exact g32p_row29_variantArithmetic_03_5 r
  · exact g32p_row29_variantArithmetic_04_5 r
  · exact g32p_row29_variantArithmetic_05_5 r
  · exact g32p_row29_variantArithmetic_06_5 r

theorem g32p_row29_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row29_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row29_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row29_variantArithmetic_00_6 r
  · exact g32p_row29_variantArithmetic_01_6 r
  · exact g32p_row29_variantArithmetic_02_6 r
  · exact g32p_row29_variantArithmetic_03_6 r
  · exact g32p_row29_variantArithmetic_04_6 r
  · exact g32p_row29_variantArithmetic_05_6 r
  · exact g32p_row29_variantArithmetic_06_6 r

theorem g32p_row29_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row29_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row29_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 28 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row29_variantArithmetic_00_7 r
  · exact g32p_row29_variantArithmetic_01_7 r
  · exact g32p_row29_variantArithmetic_02_7 r
  · exact g32p_row29_variantArithmetic_03_7 r
  · exact g32p_row29_variantArithmetic_04_7 r
  · exact g32p_row29_variantArithmetic_05_7 r
  · exact g32p_row29_variantArithmetic_06_7 r

theorem g32p_row29_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row29_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row29_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 28 c _ (g32p_row29_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row29_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 28 c _ (g32p_row29_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row29_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 28 c _ (g32p_row29_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row29_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 28 c _ (g32p_row29_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row29_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 28 c _ (g32p_row29_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row29_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 28 c _ (g32p_row29_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row29_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 28 c _ (g32p_row29_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row29_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 28 c _ (g32p_row29_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row29_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup21_source : Fin 324 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 162 then (if i.val < 81 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (81, 224)) else (if i.val < 3 then (14, 212) else (if i.val < 4 then (41, 94) else (10, 249)))) else (if i.val < 7 then (if i.val < 6 then (2, 188) else (57, 173)) else (if i.val < 8 then (14, 247) else (if i.val < 9 then (82, 247) else (43, 36))))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then (109, 19) else (11, 27)) else (if i.val < 13 then (33, 136) else (if i.val < 14 then (128, 181) else (56, 139)))) else (if i.val < 17 then (if i.val < 16 then (56, 143) else (86, 102)) else (if i.val < 18 then (86, 106) else (if i.val < 19 then (108, 70) else (53, 6)))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then (42, 35) else (118, 141)) else (if i.val < 23 then (108, 54) else (if i.val < 24 then (95, 142) else (0, 99)))) else (if i.val < 27 then (if i.val < 26 then (56, 132) else (67, 188)) else (if i.val < 28 then (33, 36) else (if i.val < 29 then (57, 154) else (29, 185))))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then (21, 194) else (86, 67)) else (if i.val < 33 then (93, 112) else (if i.val < 34 then (66, 78) else (80, 211)))) else (if i.val < 37 then (if i.val < 36 then (39, 78) else (118, 32)) else (if i.val < 38 then (120, 42) else (if i.val < 39 then (43, 74) else (86, 217))))))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then (80, 232) else (30, 140)) else (if i.val < 43 then (94, 2) else (if i.val < 44 then (41, 30) else (5, 83)))) else (if i.val < 47 then (if i.val < 46 then (83, 106) else (53, 45)) else (if i.val < 48 then (143, 9) else (if i.val < 49 then (118, 0) else (96, 123))))) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then (82, 158) else (112, 135)) else (if i.val < 53 then (85, 96) else (if i.val < 54 then (68, 15) else (96, 194)))) else (if i.val < 57 then (if i.val < 56 then (136, 130) else (94, 161)) else (if i.val < 58 then (41, 136) else (if i.val < 59 then (111, 245) else (32, 231)))))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then (95, 63) else (93, 72)) else (if i.val < 63 then (69, 64) else (if i.val < 64 then (52, 163) else (129, 159)))) else (if i.val < 67 then (if i.val < 66 then (80, 167) else (81, 206)) else (if i.val < 68 then (53, 55) else (if i.val < 69 then (108, 109) else (21, 61))))) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then (57, 216) else (81, 27)) else (if i.val < 73 then (92, 134) else (if i.val < 74 then (82, 134) else (54, 151)))) else (if i.val < 78 then (if i.val < 76 then (86, 107) else (if i.val < 77 then (86, 109) else (2, 163))) else (if i.val < 79 then (29, 157) else (if i.val < 80 then (94, 95) else (53, 8)))))))) else (if i.val < 121 then (if i.val < 101 then (if i.val < 91 then (if i.val < 86 then (if i.val < 83 then (if i.val < 82 then (21, 209) else (96, 172)) else (if i.val < 84 then (110, 20) else (if i.val < 85 then (43, 105) else (68, 170)))) else (if i.val < 88 then (if i.val < 87 then (29, 103) else (109, 155)) else (if i.val < 89 then (16, 59) else (if i.val < 90 then (56, 178) else (29, 121))))) else (if i.val < 96 then (if i.val < 93 then (if i.val < 92 then (67, 201) else (92, 45)) else (if i.val < 94 then (118, 248) else (if i.val < 95 then (67, 2) else (118, 160)))) else (if i.val < 98 then (if i.val < 97 then (93, 122) else (107, 164)) else (if i.val < 99 then (92, 64) else (if i.val < 100 then (132, 4) else (94, 68)))))) else (if i.val < 111 then (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then (81, 20) else (57, 112)) else (if i.val < 104 then (54, 13) else (if i.val < 105 then (23, 76) else (69, 10)))) else (if i.val < 108 then (if i.val < 107 then (86, 209) else (23, 133)) else (if i.val < 109 then (135, 139) else (if i.val < 110 then (142, 252) else (66, 92))))) else (if i.val < 116 then (if i.val < 113 then (if i.val < 112 then (94, 167) else (117, 221)) else (if i.val < 114 then (52, 137) else (if i.val < 115 then (81, 24) else (86, 86)))) else (if i.val < 118 then (if i.val < 117 then (92, 167) else (140, 178)) else (if i.val < 119 then (93, 28) else (if i.val < 120 then (117, 111) else (57, 200))))))) else (if i.val < 141 then (if i.val < 131 then (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then (96, 75) else (128, 217)) else (if i.val < 124 then (109, 234) else (if i.val < 125 then (86, 45) else (112, 166)))) else (if i.val < 128 then (if i.val < 127 then (67, 15) else (128, 237)) else (if i.val < 129 then (108, 119) else (if i.val < 130 then (66, 91) else (29, 120))))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 132 then (119, 25) else (129, 154)) else (if i.val < 134 then (135, 21) else (if i.val < 135 then (6, 228) else (140, 104)))) else (if i.val < 138 then (if i.val < 137 then (134, 167) else (132, 10)) else (if i.val < 139 then (140, 107) else (if i.val < 140 then (1, 161) else (108, 242)))))) else (if i.val < 151 then (if i.val < 146 then (if i.val < 143 then (if i.val < 142 then (39, 14) else (85, 110)) else (if i.val < 144 then (92, 155) else (if i.val < 145 then (128, 197) else (109, 3)))) else (if i.val < 148 then (if i.val < 147 then (5, 232) else (132, 5)) else (if i.val < 149 then (108, 234) else (if i.val < 150 then (92, 213) else (120, 164))))) else (if i.val < 156 then (if i.val < 153 then (if i.val < 152 then (82, 210) else (96, 182)) else (if i.val < 154 then (81, 98) else (if i.val < 155 then (16, 25) else (54, 39)))) else (if i.val < 159 then (if i.val < 157 then (56, 146) else (if i.val < 158 then (31, 188) else (57, 172))) else (if i.val < 160 then (130, 74) else (if i.val < 161 then (86, 37) else (31, 235))))))))) else (if i.val < 243 then (if i.val < 202 then (if i.val < 182 then (if i.val < 172 then (if i.val < 167 then (if i.val < 164 then (if i.val < 163 then (143, 7) else (10, 0)) else (if i.val < 165 then (109, 37) else (if i.val < 166 then (107, 194) else (143, 34)))) else (if i.val < 169 then (if i.val < 168 then (135, 95) else (31, 190)) else (if i.val < 170 then (11, 7) else (if i.val < 171 then (118, 30) else (81, 142))))) else (if i.val < 177 then (if i.val < 174 then (if i.val < 173 then (112, 151) else (129, 10)) else (if i.val < 175 then (15, 0) else (if i.val < 176 then (109, 226) else (31, 225)))) else (if i.val < 179 then (if i.val < 178 then (41, 221) else (10, 213)) else (if i.val < 180 then (94, 107) else (if i.val < 181 then (82, 209) else (128, 252)))))) else (if i.val < 192 then (if i.val < 187 then (if i.val < 184 then (if i.val < 183 then (65, 203) else (32, 229)) else (if i.val < 185 then (42, 248) else (if i.val < 186 then (92, 37) else (129, 204)))) else (if i.val < 189 then (if i.val < 188 then (109, 91) else (14, 213)) else (if i.val < 190 then (57, 235) else (if i.val < 191 then (57, 196) else (1, 165))))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 193 then (94, 64) else (117, 249)) else (if i.val < 195 then (86, 38) else (if i.val < 196 then (39, 19) else (109, 169)))) else (if i.val < 199 then (if i.val < 198 then (109, 198) else (81, 149)) else (if i.val < 200 then (95, 82) else (if i.val < 201 then (80, 239) else (80, 186))))))) else (if i.val < 222 then (if i.val < 212 then (if i.val < 207 then (if i.val < 204 then (if i.val < 203 then (82, 36) else (111, 236)) else (if i.val < 205 then (29, 36) else (if i.val < 206 then (112, 167) else (128, 192)))) else (if i.val < 209 then (if i.val < 208 then (86, 42) else (86, 136)) else (if i.val < 210 then (66, 201) else (if i.val < 211 then (117, 105) else (43, 101))))) else (if i.val < 217 then (if i.val < 214 then (if i.val < 213 then (23, 187) else (109, 191)) else (if i.val < 215 then (5, 188) else (if i.val < 216 then (81, 195) else (96, 4)))) else (if i.val < 219 then (if i.val < 218 then (128, 128) else (92, 69)) else (if i.val < 220 then (118, 235) else (if i.val < 221 then (94, 251) else (109, 174)))))) else (if i.val < 232 then (if i.val < 227 then (if i.val < 224 then (if i.val < 223 then (65, 102) else (119, 41)) else (if i.val < 225 then (108, 99) else (if i.val < 226 then (130, 14) else (95, 85)))) else (if i.val < 229 then (if i.val < 228 then (120, 148) else (39, 203)) else (if i.val < 230 then (95, 241) else (if i.val < 231 then (111, 235) else (118, 201))))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 233 then (83, 33) else (68, 93)) else (if i.val < 235 then (81, 44) else (if i.val < 236 then (52, 210) else (94, 133)))) else (if i.val < 240 then (if i.val < 238 then (67, 1) else (if i.val < 239 then (128, 238) else (94, 22))) else (if i.val < 241 then (23, 172) else (if i.val < 242 then (128, 226) else (52, 113)))))))) else (if i.val < 283 then (if i.val < 263 then (if i.val < 253 then (if i.val < 248 then (if i.val < 245 then (if i.val < 244 then (83, 97) else (132, 3)) else (if i.val < 246 then (68, 4) else (if i.val < 247 then (81, 166) else (96, 166)))) else (if i.val < 250 then (if i.val < 249 then (29, 39) else (131, 156)) else (if i.val < 251 then (92, 84) else (if i.val < 252 then (86, 150) else (140, 123))))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 254 then (68, 238) else (67, 149)) else (if i.val < 256 then (14, 37) else (if i.val < 257 then (40, 87) else (81, 8)))) else (if i.val < 260 then (if i.val < 259 then (112, 136) else (65, 229)) else (if i.val < 261 then (81, 168) else (if i.val < 262 then (93, 207) else (14, 208)))))) else (if i.val < 273 then (if i.val < 268 then (if i.val < 265 then (if i.val < 264 then (16, 11) else (86, 50)) else (if i.val < 266 then (5, 121) else (if i.val < 267 then (111, 242) else (134, 200)))) else (if i.val < 270 then (if i.val < 269 then (95, 214) else (95, 89)) else (if i.val < 271 then (56, 124) else (if i.val < 272 then (118, 104) else (69, 22))))) else (if i.val < 278 then (if i.val < 275 then (if i.val < 274 then (66, 218) else (128, 235)) else (if i.val < 276 then (41, 239) else (if i.val < 277 then (119, 38) else (118, 62)))) else (if i.val < 280 then (if i.val < 279 then (107, 237) else (120, 78)) else (if i.val < 281 then (82, 71) else (if i.val < 282 then (107, 212) else (15, 238))))))) else (if i.val < 303 then (if i.val < 293 then (if i.val < 288 then (if i.val < 285 then (if i.val < 284 then (41, 212) else (33, 80)) else (if i.val < 286 then (96, 26) else (if i.val < 287 then (69, 77) else (82, 85)))) else (if i.val < 290 then (if i.val < 289 then (64, 113) else (118, 173)) else (if i.val < 291 then (86, 153) else (if i.val < 292 then (22, 25) else (29, 230))))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 294 then (108, 108) else (117, 217)) else (if i.val < 296 then (65, 43) else (if i.val < 297 then (16, 64) else (43, 83)))) else (if i.val < 300 then (if i.val < 299 then (111, 241) else (53, 17)) else (if i.val < 301 then (29, 204) else (if i.val < 302 then (93, 96) else (29, 46)))))) else (if i.val < 313 then (if i.val < 308 then (if i.val < 305 then (if i.val < 304 then (2, 130) else (23, 134)) else (if i.val < 306 then (108, 17) else (if i.val < 307 then (39, 58) else (39, 243)))) else (if i.val < 310 then (if i.val < 309 then (10, 11) else (58, 7)) else (if i.val < 311 then (22, 210) else (if i.val < 312 then (118, 108) else (65, 197))))) else (if i.val < 318 then (if i.val < 315 then (if i.val < 314 then (21, 75) else (52, 143)) else (if i.val < 316 then (14, 86) else (if i.val < 317 then (41, 104) else (10, 9)))) else (if i.val < 321 then (if i.val < 319 then (64, 131) else (if i.val < 320 then (0, 79) else (117, 196))) else (if i.val < 322 then (39, 229) else (if i.val < 323 then (119, 53) else (92, 6))))))))))

def g32p_supplierGroup21_classify : Fin 324 → Fin 102 :=
  fun i => (if i.val < 162 then (if i.val < 81 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 0 else 75) else (if i.val < 3 then 76 else (if i.val < 4 then 67 else 6))) else (if i.val < 7 then (if i.val < 6 then 18 else 6) else (if i.val < 8 then 24 else (if i.val < 9 then 75 else 75)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 79 else 67) else (if i.val < 13 then 6 else (if i.val < 14 then 42 else 77))) else (if i.val < 17 then (if i.val < 16 then 76 else 6) else (if i.val < 18 then 23 else (if i.val < 19 then 75 else 42))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then 6 else 23) else (if i.val < 23 then 79 else (if i.val < 24 then 23 else 99))) else (if i.val < 27 then (if i.val < 26 then 76 else 6) else (if i.val < 28 then 6 else (if i.val < 29 then 19 else 95)))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then 44 else 39) else (if i.val < 33 then 40 else (if i.val < 34 then 75 else 77))) else (if i.val < 37 then (if i.val < 36 then 6 else 39) else (if i.val < 38 then 75 else (if i.val < 39 then 18 else 19)))))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then 79 else 78) else (if i.val < 43 then 68 else (if i.val < 44 then 79 else 78))) else (if i.val < 47 then (if i.val < 46 then 42 else 71) else (if i.val < 48 then 39 else (if i.val < 49 then 68 else 42)))) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then 77 else 40) else (if i.val < 53 then 77 else (if i.val < 54 then 6 else 75))) else (if i.val < 57 then (if i.val < 56 then 42 else 6) else (if i.val < 58 then 19 else (if i.val < 59 then 77 else 19))))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then 6 else 39) else (if i.val < 63 then 75 else (if i.val < 64 then 79 else 68))) else (if i.val < 67 then (if i.val < 66 then 42 else 77) else (if i.val < 68 then 75 else (if i.val < 69 then 42 else 18)))) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then 19 else 18) else (if i.val < 73 then 75 else (if i.val < 74 then 79 else 77))) else (if i.val < 78 then (if i.val < 76 then 6 else (if i.val < 77 then 6 else 44)) else (if i.val < 79 then 95 else (if i.val < 80 then 75 else 18))))))) else (if i.val < 121 then (if i.val < 101 then (if i.val < 91 then (if i.val < 86 then (if i.val < 83 then (if i.val < 82 then 78 else 6) else (if i.val < 84 then 42 else (if i.val < 85 then 74 else 6))) else (if i.val < 88 then (if i.val < 87 then 18 else 75) else (if i.val < 89 then 6 else (if i.val < 90 then 19 else 18)))) else (if i.val < 96 then (if i.val < 93 then (if i.val < 92 then 23 else 24) else (if i.val < 94 then 70 else (if i.val < 95 then 43 else 75))) else (if i.val < 98 then (if i.val < 97 then 74 else 42) else (if i.val < 99 then 70 else (if i.val < 100 then 39 else 74))))) else (if i.val < 111 then (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then 74 else 19) else (if i.val < 104 then 77 else (if i.val < 105 then 75 else 42))) else (if i.val < 108 then (if i.val < 107 then 6 else 18) else (if i.val < 109 then 70 else (if i.val < 110 then 39 else 74)))) else (if i.val < 116 then (if i.val < 113 then (if i.val < 112 then 6 else 39) else (if i.val < 114 then 18 else (if i.val < 115 then 18 else 19))) else (if i.val < 118 then (if i.val < 117 then 6 else 68) else (if i.val < 119 then 43 else (if i.val < 120 then 70 else 6)))))) else (if i.val < 141 then (if i.val < 131 then (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then 68 else 40) else (if i.val < 124 then 43 else (if i.val < 125 then 40 else 39))) else (if i.val < 128 then (if i.val < 127 then 68 else 42) else (if i.val < 129 then 71 else (if i.val < 130 then 74 else 71)))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 132 then 42 else 70) else (if i.val < 134 then 39 else (if i.val < 135 then 19 else 68))) else (if i.val < 138 then (if i.val < 137 then 40 else 39) else (if i.val < 139 then 68 else (if i.val < 140 then 74 else 74))))) else (if i.val < 151 then (if i.val < 146 then (if i.val < 143 then (if i.val < 142 then 24 else 19) else (if i.val < 144 then 40 else (if i.val < 145 then 42 else 42))) else (if i.val < 148 then (if i.val < 147 then 18 else 39) else (if i.val < 149 then 77 else (if i.val < 150 then 68 else 42)))) else (if i.val < 156 then (if i.val < 153 then (if i.val < 152 then 71 else 42) else (if i.val < 154 then 79 else (if i.val < 155 then 18 else 75))) else (if i.val < 159 then (if i.val < 157 then 77 else (if i.val < 158 then 71 else 23)) else (if i.val < 160 then 70 else (if i.val < 161 then 39 else 19)))))))) else (if i.val < 243 then (if i.val < 202 then (if i.val < 182 then (if i.val < 172 then (if i.val < 167 then (if i.val < 164 then (if i.val < 163 then 39 else 18) else (if i.val < 165 then 68 else (if i.val < 166 then 40 else 39))) else (if i.val < 169 then (if i.val < 168 then 68 else 76) else (if i.val < 170 then 74 else (if i.val < 171 then 74 else 71)))) else (if i.val < 177 then (if i.val < 174 then (if i.val < 173 then 39 else 68) else (if i.val < 175 then 19 else (if i.val < 176 then 75 else 19))) else (if i.val < 179 then (if i.val < 178 then 6 else 18) else (if i.val < 180 then 74 else (if i.val < 181 then 77 else 75))))) else (if i.val < 192 then (if i.val < 187 then (if i.val < 184 then (if i.val < 183 then 75 else 23) else (if i.val < 185 then 75 else (if i.val < 186 then 40 else 74))) else (if i.val < 189 then (if i.val < 188 then 42 else 78) else (if i.val < 190 then 6 else (if i.val < 191 then 23 else 95)))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 193 then 75 else 39) else (if i.val < 195 then 19 else (if i.val < 196 then 44 else 79))) else (if i.val < 199 then (if i.val < 198 then 75 else 79) else (if i.val < 200 then 23 else (if i.val < 201 then 79 else 6)))))) else (if i.val < 222 then (if i.val < 212 then (if i.val < 207 then (if i.val < 204 then (if i.val < 203 then 40 else 78) else (if i.val < 205 then 77 else (if i.val < 206 then 39 else 71))) else (if i.val < 209 then (if i.val < 208 then 19 else 19) else (if i.val < 210 then 6 else (if i.val < 211 then 75 else 77)))) else (if i.val < 217 then (if i.val < 214 then (if i.val < 213 then 75 else 42) else (if i.val < 215 then 77 else (if i.val < 216 then 75 else 71))) else (if i.val < 219 then (if i.val < 218 then 68 else 70) else (if i.val < 220 then 43 else (if i.val < 221 then 40 else 71))))) else (if i.val < 232 then (if i.val < 227 then (if i.val < 224 then (if i.val < 223 then 40 else 39) else (if i.val < 225 then 68 else (if i.val < 226 then 70 else 43))) else (if i.val < 229 then (if i.val < 228 then 70 else 19) else (if i.val < 230 then 74 else (if i.val < 231 then 71 else 40)))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 233 then 18 else 68) else (if i.val < 235 then 74 else (if i.val < 236 then 18 else 70))) else (if i.val < 240 then (if i.val < 238 then 43 else (if i.val < 239 then 70 else 75)) else (if i.val < 241 then 70 else (if i.val < 242 then 75 else 74))))))) else (if i.val < 283 then (if i.val < 263 then (if i.val < 253 then (if i.val < 248 then (if i.val < 245 then (if i.val < 244 then 71 else 40) else (if i.val < 246 then 70 else (if i.val < 247 then 79 else 71))) else (if i.val < 250 then (if i.val < 249 then 79 else 71) else (if i.val < 251 then 6 else (if i.val < 252 then 23 else 70)))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 254 then 40 else 43) else (if i.val < 256 then 95 else (if i.val < 257 then 68 else 70))) else (if i.val < 260 then (if i.val < 259 then 40 else 68) else (if i.val < 261 then 79 else (if i.val < 262 then 68 else 77))))) else (if i.val < 273 then (if i.val < 268 then (if i.val < 265 then (if i.val < 264 then 44 else 40) else (if i.val < 266 then 79 else (if i.val < 267 then 77 else 70))) else (if i.val < 270 then (if i.val < 269 then 71 else 70) else (if i.val < 271 then 78 else (if i.val < 272 then 43 else 43)))) else (if i.val < 278 then (if i.val < 275 then (if i.val < 274 then 6 else 71) else (if i.val < 276 then 43 else (if i.val < 277 then 40 else 43))) else (if i.val < 280 then (if i.val < 279 then 74 else 70) else (if i.val < 281 then 79 else (if i.val < 282 then 6 else 19)))))) else (if i.val < 303 then (if i.val < 293 then (if i.val < 288 then (if i.val < 285 then (if i.val < 284 then 18 else 6) else (if i.val < 286 then 75 else (if i.val < 287 then 75 else 79))) else (if i.val < 290 then (if i.val < 289 then 71 else 74) else (if i.val < 291 then 6 else (if i.val < 292 then 67 else 79)))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 294 then 43 else 40) else (if i.val < 296 then 74 else (if i.val < 297 then 24 else 67))) else (if i.val < 300 then (if i.val < 299 then 77 else 18) else (if i.val < 301 then 43 else (if i.val < 302 then 43 else 77))))) else (if i.val < 313 then (if i.val < 308 then (if i.val < 305 then (if i.val < 304 then 24 else 23) else (if i.val < 306 then 71 else (if i.val < 307 then 23 else 23))) else (if i.val < 310 then (if i.val < 309 then 23 else 23) else (if i.val < 311 then 75 else (if i.val < 312 then 43 else 23)))) else (if i.val < 318 then (if i.val < 315 then (if i.val < 314 then 23 else 43) else (if i.val < 316 then 75 else (if i.val < 317 then 43 else 24))) else (if i.val < 321 then (if i.val < 319 then 23 else (if i.val < 320 then 79 else 23)) else (if i.val < 322 then 6 else (if i.val < 323 then 71 else 43)))))))))

def g32p_supplierGroup21_support : Finset (Fin 102) :=
  {0, 6, 18, 19, 23, 24, 39, 40, 42, 43, 44, 67, 68, 70, 71, 74, 75, 76, 77, 78, 79, 95, 99}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup21_matrix_000 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 0 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 0 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 0 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 0 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 0 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_001 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 1 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 1 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 1 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 1 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 1 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_002 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 2 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 2 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 2 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 2 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 2 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_003 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 3 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 3 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 3 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 3 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 3 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_004 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 4 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 4 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 4 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 4 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 4 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_005 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 5 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 5 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 5 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 5 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 5 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_006 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 6 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 6 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 6 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 6 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 6 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_007 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 7 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 7 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 7 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 7 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 7 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_008 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 8 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 8 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 8 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 8 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 8 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_009 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 9 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 9 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 9 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 9 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 9 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_010 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 10 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 10 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 10 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 10 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 10 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_011 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 11 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 11 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 11 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 11 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 11 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_012 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 12 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 12 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 12 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 12 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 12 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_013 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 13 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 13 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 13 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 13 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 13 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_014 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 14 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 14 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 14 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 14 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 14 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_015 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 15 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 15 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 15 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 15 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 15 r) ∈ g32p_supplierGroup21_support := by
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

theorem g32p_supplierGroup21_matrix_016 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 16 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 16 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 16 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 16 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 16 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_017 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 17 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 17 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 17 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 17 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 17 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_018 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 18 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 18 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 18 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 18 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 18 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_019 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 19 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 19 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 19 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 19 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 19 r) ∈ g32p_supplierGroup21_support := by
  decide +kernel

theorem g32p_supplierGroup21_matrix_020 : ∀ r : Fin 16,
    g32p_row30_groupNodes (g32p_finBlockIndex 324 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 20 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup21_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup21_source (g32p_finBlockIndex 324 20 r)).1 (g32p_supplierGroup21_source (g32p_finBlockIndex 324 20 r)).2 =
      g32p_supplierGroup21_classify (g32p_finBlockIndex 324 20 r) := by
  decide +kernel

theorem g32p_supplierGroup21_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup21_classify (g32p_finBlockIndex 324 20 r) ∈ g32p_supplierGroup21_support := by
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

theorem g32p_supplierGroup21_matrix (i : Fin 324) :
    g32p_row30_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source i).1 (g32p_supplierGroup21_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row30_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup21_source i).1 (g32p_supplierGroup21_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup21_matrix_000 r
  · exact g32p_supplierGroup21_matrix_001 r
  · exact g32p_supplierGroup21_matrix_002 r
  · exact g32p_supplierGroup21_matrix_003 r
  · exact g32p_supplierGroup21_matrix_004 r
  · exact g32p_supplierGroup21_matrix_005 r
  · exact g32p_supplierGroup21_matrix_006 r
  · exact g32p_supplierGroup21_matrix_007 r
  · exact g32p_supplierGroup21_matrix_008 r
  · exact g32p_supplierGroup21_matrix_009 r
  · exact g32p_supplierGroup21_matrix_010 r
  · exact g32p_supplierGroup21_matrix_011 r
  · exact g32p_supplierGroup21_matrix_012 r
  · exact g32p_supplierGroup21_matrix_013 r
  · exact g32p_supplierGroup21_matrix_014 r
  · exact g32p_supplierGroup21_matrix_015 r
  · exact g32p_supplierGroup21_matrix_016 r
  · exact g32p_supplierGroup21_matrix_017 r
  · exact g32p_supplierGroup21_matrix_018 r
  · exact g32p_supplierGroup21_matrix_019 r
  · exact g32p_supplierGroup21_matrix_020 r

theorem g32p_supplierGroup21_class (i : Fin 324) :
    g32p_supplierForest_classes (g32p_supplierGroup21_source i).1 (g32p_supplierGroup21_source i).2 =
      g32p_supplierGroup21_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup21_source i).1 (g32p_supplierGroup21_source i).2 =
      g32p_supplierGroup21_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup21_class_000 r
  · exact g32p_supplierGroup21_class_001 r
  · exact g32p_supplierGroup21_class_002 r
  · exact g32p_supplierGroup21_class_003 r
  · exact g32p_supplierGroup21_class_004 r
  · exact g32p_supplierGroup21_class_005 r
  · exact g32p_supplierGroup21_class_006 r
  · exact g32p_supplierGroup21_class_007 r
  · exact g32p_supplierGroup21_class_008 r
  · exact g32p_supplierGroup21_class_009 r
  · exact g32p_supplierGroup21_class_010 r
  · exact g32p_supplierGroup21_class_011 r
  · exact g32p_supplierGroup21_class_012 r
  · exact g32p_supplierGroup21_class_013 r
  · exact g32p_supplierGroup21_class_014 r
  · exact g32p_supplierGroup21_class_015 r
  · exact g32p_supplierGroup21_class_016 r
  · exact g32p_supplierGroup21_class_017 r
  · exact g32p_supplierGroup21_class_018 r
  · exact g32p_supplierGroup21_class_019 r
  · exact g32p_supplierGroup21_class_020 r

theorem g32p_supplierGroup21_support_mem (i : Fin 324) :
    g32p_supplierGroup21_classify i ∈ g32p_supplierGroup21_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup21_classify i ∈ g32p_supplierGroup21_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup21_support_000 r
  · exact g32p_supplierGroup21_support_001 r
  · exact g32p_supplierGroup21_support_002 r
  · exact g32p_supplierGroup21_support_003 r
  · exact g32p_supplierGroup21_support_004 r
  · exact g32p_supplierGroup21_support_005 r
  · exact g32p_supplierGroup21_support_006 r
  · exact g32p_supplierGroup21_support_007 r
  · exact g32p_supplierGroup21_support_008 r
  · exact g32p_supplierGroup21_support_009 r
  · exact g32p_supplierGroup21_support_010 r
  · exact g32p_supplierGroup21_support_011 r
  · exact g32p_supplierGroup21_support_012 r
  · exact g32p_supplierGroup21_support_013 r
  · exact g32p_supplierGroup21_support_014 r
  · exact g32p_supplierGroup21_support_015 r
  · exact g32p_supplierGroup21_support_016 r
  · exact g32p_supplierGroup21_support_017 r
  · exact g32p_supplierGroup21_support_018 r
  · exact g32p_supplierGroup21_support_019 r
  · exact g32p_supplierGroup21_support_020 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row30_supplierClassifier : Fin 324 → Fin 102 := g32p_supplierGroup21_classify

theorem g32p_row30_groupEquiv_isConj (i : Fin 324) :
    IsConj (g32p_row30_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row30_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup21_source i).1 (g32p_supplierGroup21_source i).2
  rw [g32p_supplierGroup21_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row30_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup21_matrix i)

def g32p_row30_supplierClass (h : (g32p_recordedSuppliers 29).H) : Fin 102 :=
  g32p_row30_supplierClassifier (g32p_row30_groupEquiv.symm h)

theorem g32p_row30_supplierClass_isConj (h : (g32p_recordedSuppliers 29).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row30_supplierClass h)) := by
  have he : (g32p_row30_groupEquiv (g32p_row30_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 29).H => (a : g32p_G))
      (g32p_row30_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row30_supplierClassifier (g32p_row30_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row30_groupEquiv_isConj (g32p_row30_groupEquiv.symm h)

theorem g32p_row30_supplierClass_iff (h : (g32p_recordedSuppliers 29).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row30_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row30_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row30_supplierClass_isConj h).symm

theorem g32p_row30_supplierClass_mem_support (h : (g32p_recordedSuppliers 29).H) :
    g32p_row30_supplierClass h ∈ g32p_supplierGroup21_support :=
  g32p_supplierGroup21_support_mem (g32p_row30_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end
