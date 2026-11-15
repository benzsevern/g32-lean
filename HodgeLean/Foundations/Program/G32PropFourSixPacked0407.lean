import HodgeLean.Foundations.Program.G32PropFourSixPacked0406
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixPacked0357
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row28_generatorIndex : Fin 8 → Fin 408 :=
  ![27, 78, 129, 180, 258, 259, 360, 361]

theorem g32p_row28_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup07_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 27 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 27 g32p_row28_supplierClass
    g32p_row28_supplierClass_isConj g32p_supplierGroup07_support g32p_row28_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row28_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup07_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row28_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 27 c false (g32p_row28_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 27 c true (g32p_row28_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 27 c false (g32p_row28_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 27 c true (g32p_row28_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 27 c false (g32p_row28_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 27 c false (g32p_row28_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 27 c true (g32p_row28_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 27 c true (g32p_row28_coinduced_zero c hc true) 3

theorem g32p_row28_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row28_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row28_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row28_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row28_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row28_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row28_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row28_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row28_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row28_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row28_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row28_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row28_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup07_support →
      g32p_literalTraceValue (g32p_row28_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row28_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup07_support) :
    g32p_literalTraceValue (g32p_row28_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup07_support →
    g32p_literalTraceValue (g32p_row28_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row28_zeroTrace_block_00 r k
  · exact g32p_row28_zeroTrace_block_01 r k
  · exact g32p_row28_zeroTrace_block_02 r k
  · exact g32p_row28_zeroTrace_block_03 r k
  · exact g32p_row28_zeroTrace_block_04 r k
  · exact g32p_row28_zeroTrace_block_05 r k
  · exact g32p_row28_zeroTrace_block_06 r k

theorem g32p_row28_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup07_support) :
    (g32p_recordedInductionGenerators (g32p_row28_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row28_generatorIndex k) c) := by
  rw [g32p_row28_recordedGenerator_zero c hc k, g32p_row28_zeroTrace_arithmetic c k hc]
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

def g32p_row28_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [11664, 11664, 11664])) else (if i.val < 4 then [] else (if i.val < 5 then [1944, 1944, 1944] else []))) else (if i.val < 9 then (if i.val < 7 then [3888, 3888, 3888] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [486, 486, 486] else (if i.val < 11 then [] else [1944, 1944, 1944])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [486, 486, 486, 486] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else [-1944, 0, 1944, 1944]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [-7776, 3888] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [-1944, 1944, 3888, 3888] else [0, 486])) else (if i.val < 36 then (if i.val < 35 then [] else [3888, 3888, 3888]) else (if i.val < 37 then [486, 486, 486] else [155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [0, 486] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [486, 486, 486] else []))) else (if i.val < 47 then (if i.val < 45 then [3888, 3888, 11664, 11664] else (if i.val < 46 then [3888, 3888, 3888] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [0, 486])) else (if i.val < 55 then [] else (if i.val < 56 then [] else [-1944, 0, 1944, 1944]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [486, 486, 486, 486])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [11664, 11664, 11664] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [486, 486, 486, 486] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else [-1944, 1944, 3888, 3888]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [1944, 1944, 1944])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [-1944, 1944, 3888, 3888])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [3888, 3888, 11664, 11664])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [-1944, 0, 1944, 1944] else (if i.val < 94 then [-7776, 3888] else []))) else (if i.val < 98 then (if i.val < 96 then [-7776, 3888] else (if i.val < 97 then [] else [155520, 155520])) else (if i.val < 100 then (if i.val < 99 then [3888, 3888, 11664, 11664] else [155520, 155520]) else (if i.val < 101 then [11664, 11664, 11664] else [])))))))

theorem g32p_row28_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup07_support) :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row28_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row28_characterValues j)).val) c) (g32p_literalTraceValue 27 c)
      [1, -1, 1] (g32p_row28_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row28_tracePolynomial_000
  · exact g32p_row28_tracePolynomial_001
  · exact g32p_row28_tracePolynomial_002
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_009
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_011
  · exact g32p_row28_tracePolynomial_012
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_014
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (18 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_032
  · exact g32p_row28_tracePolynomial_033
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_035
  · exact g32p_row28_tracePolynomial_036
  · exact g32p_row28_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_039
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_042
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_044
  · exact g32p_row28_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_053
  · exact g32p_row28_tracePolynomial_054
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_062
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_067
  · exact g32p_row28_tracePolynomial_068
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_070
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_075
  · exact g32p_row28_tracePolynomial_076
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_087
  · exact g32p_row28_tracePolynomial_088
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_092
  · exact g32p_row28_tracePolynomial_093
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup07_support) hc)
  · exact g32p_row28_tracePolynomial_095
  · exact g32p_row28_tracePolynomial_096
  · exact g32p_row28_tracePolynomial_097
  · exact g32p_row28_tracePolynomial_098
  · exact g32p_row28_tracePolynomial_099
  · exact g32p_row28_tracePolynomial_100
  · exact g32p_row28_tracePolynomial_101

theorem g32p_row28_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 27 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 27 c) := by
  by_cases hc : c ∈ g32p_supplierGroup07_support
  · have hclass (j : Fin 486) :
        IsConj (g32p_literalRepresentative c) (g32p_row09_groupEquiv j : g32p_G) ↔
          g32p_row28_supplierClassifier j = c := by
      simpa only [g32p_row28_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row28_supplierClass_iff (g32p_row09_groupEquiv j) c
    have hχ (j : Fin 486) :
        (g32p_recordedSupplierCharacters 27 (g32p_row09_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row28_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 27 (show (g32p_recordedSuppliers 27).H from g32p_row09_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row28_characterValues (g32p_row09_groupEquiv.symm (g32p_row09_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 27).H (g32p_recordedSupplierCharacters 27)
      (g32p_literalRepresentative c) g32p_row09_groupEquiv g32p_row28_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row28_characterValues j)).val) c 6 486
      (g32p_literalCentralizer c) (g32p_literalTraceValue 27 c) [1, -1, 1]
      (g32p_row28_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row28_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 27)))
      (g32p_row28_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row28_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row28_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
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

theorem g32p_row28_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
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

theorem g32p_row28_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
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

theorem g32p_row28_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
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

theorem g32p_row28_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
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

theorem g32p_row28_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
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

theorem g32p_row28_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row28_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row28_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
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

theorem g32p_row28_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row28_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row28_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row28_variantArithmetic_00_0 r
  · exact g32p_row28_variantArithmetic_01_0 r
  · exact g32p_row28_variantArithmetic_02_0 r
  · exact g32p_row28_variantArithmetic_03_0 r
  · exact g32p_row28_variantArithmetic_04_0 r
  · exact g32p_row28_variantArithmetic_05_0 r
  · exact g32p_row28_variantArithmetic_06_0 r

theorem g32p_row28_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row28_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row28_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row28_variantArithmetic_00_1 r
  · exact g32p_row28_variantArithmetic_01_1 r
  · exact g32p_row28_variantArithmetic_02_1 r
  · exact g32p_row28_variantArithmetic_03_1 r
  · exact g32p_row28_variantArithmetic_04_1 r
  · exact g32p_row28_variantArithmetic_05_1 r
  · exact g32p_row28_variantArithmetic_06_1 r

theorem g32p_row28_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row28_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row28_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row28_variantArithmetic_00_2 r
  · exact g32p_row28_variantArithmetic_01_2 r
  · exact g32p_row28_variantArithmetic_02_2 r
  · exact g32p_row28_variantArithmetic_03_2 r
  · exact g32p_row28_variantArithmetic_04_2 r
  · exact g32p_row28_variantArithmetic_05_2 r
  · exact g32p_row28_variantArithmetic_06_2 r

theorem g32p_row28_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row28_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row28_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row28_variantArithmetic_00_3 r
  · exact g32p_row28_variantArithmetic_01_3 r
  · exact g32p_row28_variantArithmetic_02_3 r
  · exact g32p_row28_variantArithmetic_03_3 r
  · exact g32p_row28_variantArithmetic_04_3 r
  · exact g32p_row28_variantArithmetic_05_3 r
  · exact g32p_row28_variantArithmetic_06_3 r

theorem g32p_row28_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row28_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row28_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row28_variantArithmetic_00_4 r
  · exact g32p_row28_variantArithmetic_01_4 r
  · exact g32p_row28_variantArithmetic_02_4 r
  · exact g32p_row28_variantArithmetic_03_4 r
  · exact g32p_row28_variantArithmetic_04_4 r
  · exact g32p_row28_variantArithmetic_05_4 r
  · exact g32p_row28_variantArithmetic_06_4 r

theorem g32p_row28_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row28_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row28_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row28_variantArithmetic_00_5 r
  · exact g32p_row28_variantArithmetic_01_5 r
  · exact g32p_row28_variantArithmetic_02_5 r
  · exact g32p_row28_variantArithmetic_03_5 r
  · exact g32p_row28_variantArithmetic_04_5 r
  · exact g32p_row28_variantArithmetic_05_5 r
  · exact g32p_row28_variantArithmetic_06_5 r

theorem g32p_row28_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row28_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row28_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row28_variantArithmetic_00_6 r
  · exact g32p_row28_variantArithmetic_01_6 r
  · exact g32p_row28_variantArithmetic_02_6 r
  · exact g32p_row28_variantArithmetic_03_6 r
  · exact g32p_row28_variantArithmetic_04_6 r
  · exact g32p_row28_variantArithmetic_05_6 r
  · exact g32p_row28_variantArithmetic_06_6 r

theorem g32p_row28_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row28_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row28_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 27 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row28_variantArithmetic_00_7 r
  · exact g32p_row28_variantArithmetic_01_7 r
  · exact g32p_row28_variantArithmetic_02_7 r
  · exact g32p_row28_variantArithmetic_03_7 r
  · exact g32p_row28_variantArithmetic_04_7 r
  · exact g32p_row28_variantArithmetic_05_7 r
  · exact g32p_row28_variantArithmetic_06_7 r

theorem g32p_row28_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row28_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row28_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 27 c _ (g32p_row28_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row28_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 27 c _ (g32p_row28_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row28_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 27 c _ (g32p_row28_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row28_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 27 c _ (g32p_row28_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row28_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 27 c _ (g32p_row28_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row28_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 27 c _ (g32p_row28_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row28_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 27 c _ (g32p_row28_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row28_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 27 c _ (g32p_row28_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row28_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row29_supplierClassifier : Fin 486 → Fin 102 := g32p_supplierGroup07_classify

theorem g32p_row29_groupEquiv_isConj (i : Fin 486) :
    IsConj (g32p_row09_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row29_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup07_source i).1 (g32p_supplierGroup07_source i).2
  rw [g32p_supplierGroup07_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row09_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup07_matrix i)

def g32p_row29_supplierClass (h : (g32p_recordedSuppliers 28).H) : Fin 102 :=
  g32p_row29_supplierClassifier (g32p_row09_groupEquiv.symm h)

theorem g32p_row29_supplierClass_isConj (h : (g32p_recordedSuppliers 28).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row29_supplierClass h)) := by
  have he : (g32p_row09_groupEquiv (g32p_row09_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 28).H => (a : g32p_G))
      (g32p_row09_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row29_supplierClassifier (g32p_row09_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row29_groupEquiv_isConj (g32p_row09_groupEquiv.symm h)

theorem g32p_row29_supplierClass_iff (h : (g32p_recordedSuppliers 28).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row29_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row29_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row29_supplierClass_isConj h).symm

theorem g32p_row29_supplierClass_mem_support (h : (g32p_recordedSuppliers 28).H) :
    g32p_row29_supplierClass h ∈ g32p_supplierGroup07_support :=
  g32p_supplierGroup07_support_mem (g32p_row09_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row29_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 0) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 0) (g32p_literalTraceValue 28 0)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_000]
  decide +kernel

theorem g32p_row29_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 1 = [0, 1, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 1) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 1) (g32p_literalTraceValue 28 1)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row29_traceCoefficients_001]
  decide +kernel

theorem g32p_row29_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 2 = [0, 3, 1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 2) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 2) (g32p_literalTraceValue 28 2)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row29_traceCoefficients_002]
  decide +kernel

theorem g32p_row29_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 4 = [3, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 4) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 4) (g32p_literalTraceValue 28 4)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_004]
  decide +kernel

theorem g32p_row29_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 6 = [6, 12, 12] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 6) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 6) (g32p_literalTraceValue 28 6)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row29_traceCoefficients_006]
  decide +kernel

theorem g32p_row29_traceCoefficients_009 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 9 = [9, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_009 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 9) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 9) (g32p_literalTraceValue 28 9)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_009]
  decide +kernel

theorem g32p_row29_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 11 = [3, 0, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 11) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 11) (g32p_literalTraceValue 28 11)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row29_traceCoefficients_011]
  decide +kernel

theorem g32p_row29_traceCoefficients_012 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 12 = [0, 9, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_012 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 12) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 12) (g32p_literalTraceValue 28 12)
      [1, 1, 1] [486] = true := by
  rw [g32p_row29_traceCoefficients_012]
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

theorem g32p_row29_traceCoefficients_014 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 14 = [9, 0, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_014 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 14) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 14) (g32p_literalTraceValue 28 14)
      [1, 1, 1] [486] = true := by
  rw [g32p_row29_traceCoefficients_014]
  decide +kernel

theorem g32p_row29_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 24 = [0, 3, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 24) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 24) (g32p_literalTraceValue 28 24)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row29_traceCoefficients_024]
  decide +kernel

theorem g32p_row29_traceCoefficients_028 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 28 = [3, 1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_028 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 28) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 28) (g32p_literalTraceValue 28 28)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_028]
  decide +kernel

theorem g32p_row29_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 32 = [12, 12, 6] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 32) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 32) (g32p_literalTraceValue 28 32)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row29_traceCoefficients_032]
  decide +kernel

theorem g32p_row29_traceCoefficients_033 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 33 = [0, 9, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_033 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 33) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 33) (g32p_literalTraceValue 28 33)
      [1, 1, 1] [486] = true := by
  rw [g32p_row29_traceCoefficients_033]
  decide +kernel

theorem g32p_row29_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 35 = [12, 12, 6] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 35) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 35) (g32p_literalTraceValue 28 35)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row29_traceCoefficients_035]
  decide +kernel

theorem g32p_row29_traceCoefficients_036 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 36 = [0, 9, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_036 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 36) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 36) (g32p_literalTraceValue 28 36)
      [1, 1, 1] [486] = true := by
  rw [g32p_row29_traceCoefficients_036]
  decide +kernel

theorem g32p_row29_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 37 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 37) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 37) (g32p_literalTraceValue 28 37)
      [1, 1, 1] [155520] = true := by
  rw [g32p_row29_traceCoefficients_037]
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

theorem g32p_row29_traceCoefficients_039 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 39 = [9, 0, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_039 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 39) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 39) (g32p_literalTraceValue 28 39)
      [1, 1, 1] [486] = true := by
  rw [g32p_row29_traceCoefficients_039]
  decide +kernel

theorem g32p_row29_traceCoefficients_042 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 42 = [9, 0, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_042 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 42) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 42) (g32p_literalTraceValue 28 42)
      [1, 1, 1] [486] = true := by
  rw [g32p_row29_traceCoefficients_042]
  decide +kernel

theorem g32p_row29_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 44 = [1, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 44) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 44) (g32p_literalTraceValue 28 44)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_044]
  decide +kernel

theorem g32p_row29_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 45 = [12, 6, 12] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 45) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 45) (g32p_literalTraceValue 28 45)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row29_traceCoefficients_045]
  decide +kernel

theorem g32p_row29_traceCoefficients_053 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 53 = [9, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_053 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 53) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 53) (g32p_literalTraceValue 28 53)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_053]
  decide +kernel

theorem g32p_row29_traceCoefficients_054 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 54 = [0, 9, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_054 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 54) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 54) (g32p_literalTraceValue 28 54)
      [1, 1, 1] [486] = true := by
  rw [g32p_row29_traceCoefficients_054]
  decide +kernel

theorem g32p_row29_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 56 = [3, 0, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 56) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 56) (g32p_literalTraceValue 28 56)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row29_traceCoefficients_056]
  decide +kernel

theorem g32p_row29_traceCoefficients_062 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 62 = [9, 0, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_062 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 62) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 62) (g32p_literalTraceValue 28 62)
      [1, 1, 1] [486] = true := by
  rw [g32p_row29_traceCoefficients_062]
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

theorem g32p_row29_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 67 = [1, 0, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 67) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 67) (g32p_literalTraceValue 28 67)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row29_traceCoefficients_067]
  decide +kernel

theorem g32p_row29_traceCoefficients_068 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 68 = [9, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_068 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 68) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 68) (g32p_literalTraceValue 28 68)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_068]
  decide +kernel

theorem g32p_row29_traceCoefficients_070 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 70 = [9, 9] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_070 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 70) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 70) (g32p_literalTraceValue 28 70)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_070]
  decide +kernel

theorem g32p_row29_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 75 = [6, 12, 12] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 75) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 75) (g32p_literalTraceValue 28 75)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row29_traceCoefficients_075]
  decide +kernel

theorem g32p_row29_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 76 = [1, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 76) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 76) (g32p_literalTraceValue 28 76)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_076]
  decide +kernel

theorem g32p_row29_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 78 = [0, 3, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 78) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 78) (g32p_literalTraceValue 28 78)
      [1, 1, 1] [1944] = true := by
  rw [g32p_row29_traceCoefficients_078]
  decide +kernel

theorem g32p_row29_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 84 = [12, 6, 12] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 84) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 84) (g32p_literalTraceValue 28 84)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row29_traceCoefficients_084]
  decide +kernel

theorem g32p_row29_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 87 = [3, 0, 1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 87) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 87) (g32p_literalTraceValue 28 87)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row29_traceCoefficients_087]
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

theorem g32p_row29_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 88 = [3, 0, 1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 88) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 88) (g32p_literalTraceValue 28 88)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row29_traceCoefficients_088]
  decide +kernel

theorem g32p_row29_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 92 = [3, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 92) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 92) (g32p_literalTraceValue 28 92)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_092]
  decide +kernel

theorem g32p_row29_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 93 = [0, 3, 1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 93) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 93) (g32p_literalTraceValue 28 93)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row29_traceCoefficients_093]
  decide +kernel

theorem g32p_row29_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 95 = [1, 0, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 95) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 95) (g32p_literalTraceValue 28 95)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row29_traceCoefficients_095]
  decide +kernel

theorem g32p_row29_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 96 = [0, 1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 96) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 96) (g32p_literalTraceValue 28 96)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_096]
  decide +kernel

theorem g32p_row29_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 97 = [0, 1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 97) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 97) (g32p_literalTraceValue 28 97)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_097]
  decide +kernel

theorem g32p_row29_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 98 = [0, 1, 3] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 98) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 98) (g32p_literalTraceValue 28 98)
      [1, 1, 1] [11664] = true := by
  rw [g32p_row29_traceCoefficients_098]
  decide +kernel

theorem g32p_row29_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 99 = [1] := by
  decide +kernel

theorem g32p_row29_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 486 (g32p_literalCentralizer 99) 3
      (g32p_supplierTraceCoefficients g32p_row29_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row29_characterValues j)).val) 99) (g32p_literalTraceValue 28 99)
      [1, 1, 1] [] = true := by
  rw [g32p_row29_traceCoefficients_099]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
