import HodgeLean.Foundations.Program.G32PropFourSixPacked0409
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow32
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row31_supplierClassifier : Fin 18 → Fin 102 := g32p_supplierGroup22_classify

theorem g32p_row31_groupEquiv_isConj (i : Fin 18) :
    IsConj (g32p_row31_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row31_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup22_source i).1 (g32p_supplierGroup22_source i).2
  rw [g32p_supplierGroup22_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row31_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup22_matrix i)

def g32p_row31_supplierClass (h : (g32p_recordedSuppliers 30).H) : Fin 102 :=
  g32p_row31_supplierClassifier (g32p_row31_groupEquiv.symm h)

theorem g32p_row31_supplierClass_isConj (h : (g32p_recordedSuppliers 30).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row31_supplierClass h)) := by
  have he : (g32p_row31_groupEquiv (g32p_row31_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 30).H => (a : g32p_G))
      (g32p_row31_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row31_supplierClassifier (g32p_row31_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row31_groupEquiv_isConj (g32p_row31_groupEquiv.symm h)

theorem g32p_row31_supplierClass_iff (h : (g32p_recordedSuppliers 30).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row31_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row31_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row31_supplierClass_isConj h).symm

theorem g32p_row31_supplierClass_mem_support (h : (g32p_recordedSuppliers 30).H) :
    g32p_row31_supplierClass h ∈ g32p_supplierGroup22_support :=
  g32p_supplierGroup22_support_mem (g32p_row31_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row31_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 0) (g32p_literalTraceValue 30 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row31_traceCoefficients_000]
  decide +kernel

theorem g32p_row31_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 4 = [0, 0, 1, 0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 4) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 4) (g32p_literalTraceValue 30 4)
      [1, -1, 1] [648, 648, 648] = true := by
  rw [g32p_row31_traceCoefficients_004]
  decide +kernel

theorem g32p_row31_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 11 = [0, 0, 1, 0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 11) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 11) (g32p_literalTraceValue 30 11)
      [1, -1, 1] [648, 648, 648] = true := by
  rw [g32p_row31_traceCoefficients_011]
  decide +kernel

theorem g32p_row31_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 18 = [0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 18) (g32p_literalTraceValue 30 18)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row31_traceCoefficients_018]
  decide +kernel

theorem g32p_row31_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 25 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 25) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 25) (g32p_literalTraceValue 30 25)
      [1, -1, 1] [0, 0, 108, 108] = true := by
  rw [g32p_row31_traceCoefficients_025]
  decide +kernel

theorem g32p_row31_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 29 = [0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 29) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 29) (g32p_literalTraceValue 30 29)
      [1, -1, 1] [-108] = true := by
  rw [g32p_row31_traceCoefficients_029]
  decide +kernel

theorem g32p_row31_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 43 = [0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 43) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 43) (g32p_literalTraceValue 30 43)
      [1, -1, 1] [-108] = true := by
  rw [g32p_row31_traceCoefficients_043]
  decide +kernel

theorem g32p_row31_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 50 = [0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 50) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 50) (g32p_literalTraceValue 30 50)
      [1, -1, 1] [-108] = true := by
  rw [g32p_row31_traceCoefficients_050]
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

theorem g32p_row31_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 59 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 59) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 59) (g32p_literalTraceValue 30 59)
      [1, -1, 1] [0, 0, 108, 108] = true := by
  rw [g32p_row31_traceCoefficients_059]
  decide +kernel

theorem g32p_row31_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 65 = [0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 65) (g32p_literalTraceValue 30 65)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row31_traceCoefficients_065]
  decide +kernel

theorem g32p_row31_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 74 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 74) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 74) (g32p_literalTraceValue 30 74)
      [1, -1, 1] [0, 0, 108, 108] = true := by
  rw [g32p_row31_traceCoefficients_074]
  decide +kernel

theorem g32p_row31_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 78 = [0, 0, 1, 0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 78) (g32p_literalTraceValue 30 78)
      [1, -1, 1] [648, 648, 648] = true := by
  rw [g32p_row31_traceCoefficients_078]
  decide +kernel

theorem g32p_row31_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 82 = [0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 82) (g32p_literalTraceValue 30 82)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row31_traceCoefficients_082]
  decide +kernel

theorem g32p_row31_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 96 = [1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 96) (g32p_literalTraceValue 30 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row31_traceCoefficients_096]
  decide +kernel

theorem g32p_row31_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 101 = [1] := by
  decide +kernel

theorem g32p_row31_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer 101) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) 101) (g32p_literalTraceValue 30 101)
      [1, -1, 1] [] = true := by
  rw [g32p_row31_traceCoefficients_101]
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

def g32p_row31_generatorIndex : Fin 8 → Fin 408 :=
  ![30, 81, 132, 183, 264, 265, 366, 367]

theorem g32p_row31_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup22_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 30 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 30 g32p_row31_supplierClass
    g32p_row31_supplierClass_isConj g32p_supplierGroup22_support g32p_row31_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row31_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup22_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row31_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 30 c false (g32p_row31_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 30 c true (g32p_row31_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 30 c false (g32p_row31_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 30 c true (g32p_row31_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 30 c false (g32p_row31_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 30 c false (g32p_row31_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 30 c true (g32p_row31_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 30 c true (g32p_row31_coinduced_zero c hc true) 3

theorem g32p_row31_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup22_support →
      g32p_literalTraceValue (g32p_row31_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row31_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup22_support →
      g32p_literalTraceValue (g32p_row31_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row31_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup22_support →
      g32p_literalTraceValue (g32p_row31_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row31_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup22_support →
      g32p_literalTraceValue (g32p_row31_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row31_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup22_support →
      g32p_literalTraceValue (g32p_row31_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row31_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup22_support →
      g32p_literalTraceValue (g32p_row31_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row31_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup22_support →
      g32p_literalTraceValue (g32p_row31_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row31_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup22_support) :
    g32p_literalTraceValue (g32p_row31_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup22_support →
    g32p_literalTraceValue (g32p_row31_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row31_zeroTrace_block_00 r k
  · exact g32p_row31_zeroTrace_block_01 r k
  · exact g32p_row31_zeroTrace_block_02 r k
  · exact g32p_row31_zeroTrace_block_03 r k
  · exact g32p_row31_zeroTrace_block_04 r k
  · exact g32p_row31_zeroTrace_block_05 r k
  · exact g32p_row31_zeroTrace_block_06 r k

theorem g32p_row31_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup22_support) :
    (g32p_recordedInductionGenerators (g32p_row31_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row31_generatorIndex k) c) := by
  rw [g32p_row31_recordedGenerator_zero c hc k, g32p_row31_zeroTrace_arithmetic c k hc]
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

def g32p_row31_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [648, 648, 648] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [648, 648, 648])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [1728, 1728] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [0, 0, 108, 108] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [-108] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else [-108]))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [-108])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [0, 0, 108, 108])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [1728, 1728])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [0, 0, 108, 108] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [648, 648, 648])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [1728, 1728] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [])))))))

theorem g32p_row31_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup22_support) :
    g32p_supplierTracePolynomialCheck 18 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) c) (g32p_literalTraceValue 30 c)
      [1, -1, 1] (g32p_row31_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row31_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_043
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_050
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_074
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_082
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_096
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (99 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup22_support) hc)
  · exact g32p_row31_tracePolynomial_101

theorem g32p_row31_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 30 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 30 c) := by
  by_cases hc : c ∈ g32p_supplierGroup22_support
  · have hclass (j : Fin 18) :
        IsConj (g32p_literalRepresentative c) (g32p_row31_groupEquiv j : g32p_G) ↔
          g32p_row31_supplierClassifier j = c := by
      simpa only [g32p_row31_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row31_supplierClass_iff (g32p_row31_groupEquiv j) c
    have hχ (j : Fin 18) :
        (g32p_recordedSupplierCharacters 30 (g32p_row31_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row31_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 30 (show (g32p_recordedSuppliers 30).H from g32p_row31_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row31_characterValues (g32p_row31_groupEquiv.symm (g32p_row31_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 30).H (g32p_recordedSupplierCharacters 30)
      (g32p_literalRepresentative c) g32p_row31_groupEquiv g32p_row31_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row31_characterValues j)).val) c 6 18
      (g32p_literalCentralizer c) (g32p_literalTraceValue 30 c) [1, -1, 1]
      (g32p_row31_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row31_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 30)))
      (g32p_row31_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row31_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row31_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
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

theorem g32p_row31_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
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

theorem g32p_row31_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
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

theorem g32p_row31_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
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

theorem g32p_row31_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
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

theorem g32p_row31_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
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

theorem g32p_row31_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row31_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row31_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
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

theorem g32p_row31_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row31_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row31_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row31_variantArithmetic_00_0 r
  · exact g32p_row31_variantArithmetic_01_0 r
  · exact g32p_row31_variantArithmetic_02_0 r
  · exact g32p_row31_variantArithmetic_03_0 r
  · exact g32p_row31_variantArithmetic_04_0 r
  · exact g32p_row31_variantArithmetic_05_0 r
  · exact g32p_row31_variantArithmetic_06_0 r

theorem g32p_row31_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row31_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row31_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row31_variantArithmetic_00_1 r
  · exact g32p_row31_variantArithmetic_01_1 r
  · exact g32p_row31_variantArithmetic_02_1 r
  · exact g32p_row31_variantArithmetic_03_1 r
  · exact g32p_row31_variantArithmetic_04_1 r
  · exact g32p_row31_variantArithmetic_05_1 r
  · exact g32p_row31_variantArithmetic_06_1 r

theorem g32p_row31_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row31_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row31_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row31_variantArithmetic_00_2 r
  · exact g32p_row31_variantArithmetic_01_2 r
  · exact g32p_row31_variantArithmetic_02_2 r
  · exact g32p_row31_variantArithmetic_03_2 r
  · exact g32p_row31_variantArithmetic_04_2 r
  · exact g32p_row31_variantArithmetic_05_2 r
  · exact g32p_row31_variantArithmetic_06_2 r

theorem g32p_row31_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row31_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row31_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row31_variantArithmetic_00_3 r
  · exact g32p_row31_variantArithmetic_01_3 r
  · exact g32p_row31_variantArithmetic_02_3 r
  · exact g32p_row31_variantArithmetic_03_3 r
  · exact g32p_row31_variantArithmetic_04_3 r
  · exact g32p_row31_variantArithmetic_05_3 r
  · exact g32p_row31_variantArithmetic_06_3 r

theorem g32p_row31_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row31_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row31_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row31_variantArithmetic_00_4 r
  · exact g32p_row31_variantArithmetic_01_4 r
  · exact g32p_row31_variantArithmetic_02_4 r
  · exact g32p_row31_variantArithmetic_03_4 r
  · exact g32p_row31_variantArithmetic_04_4 r
  · exact g32p_row31_variantArithmetic_05_4 r
  · exact g32p_row31_variantArithmetic_06_4 r

theorem g32p_row31_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row31_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row31_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row31_variantArithmetic_00_5 r
  · exact g32p_row31_variantArithmetic_01_5 r
  · exact g32p_row31_variantArithmetic_02_5 r
  · exact g32p_row31_variantArithmetic_03_5 r
  · exact g32p_row31_variantArithmetic_04_5 r
  · exact g32p_row31_variantArithmetic_05_5 r
  · exact g32p_row31_variantArithmetic_06_5 r

theorem g32p_row31_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row31_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row31_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row31_variantArithmetic_00_6 r
  · exact g32p_row31_variantArithmetic_01_6 r
  · exact g32p_row31_variantArithmetic_02_6 r
  · exact g32p_row31_variantArithmetic_03_6 r
  · exact g32p_row31_variantArithmetic_04_6 r
  · exact g32p_row31_variantArithmetic_05_6 r
  · exact g32p_row31_variantArithmetic_06_6 r

theorem g32p_row31_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row31_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row31_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 30 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row31_variantArithmetic_00_7 r
  · exact g32p_row31_variantArithmetic_01_7 r
  · exact g32p_row31_variantArithmetic_02_7 r
  · exact g32p_row31_variantArithmetic_03_7 r
  · exact g32p_row31_variantArithmetic_04_7 r
  · exact g32p_row31_variantArithmetic_05_7 r
  · exact g32p_row31_variantArithmetic_06_7 r

theorem g32p_row31_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row31_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row31_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 30 c _ (g32p_row31_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row31_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 30 c _ (g32p_row31_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row31_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 30 c _ (g32p_row31_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row31_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 30 c _ (g32p_row31_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row31_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 30 c _ (g32p_row31_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row31_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 30 c _ (g32p_row31_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row31_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 30 c _ (g32p_row31_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row31_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 30 c _ (g32p_row31_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row31_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup23_source : Fin 648 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 324 then (if i.val < 162 then (if i.val < 81 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (142, 18)) else (if i.val < 3 then (2, 64) else (if i.val < 4 then (0, 101) else (29, 134)))) else (if i.val < 7 then (if i.val < 6 then (116, 226) else (127, 30)) else (if i.val < 8 then (139, 197) else (if i.val < 9 then (45, 70) else (98, 8))))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then (0, 96) else (129, 194)) else (if i.val < 13 then (88, 194) else (if i.val < 14 then (79, 107) else (19, 178)))) else (if i.val < 17 then (if i.val < 16 then (12, 45) else (143, 120)) else (if i.val < 18 then (74, 235) else (if i.val < 19 then (142, 192) else (136, 224)))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then (143, 139) else (141, 169)) else (if i.val < 23 then (0, 99) else (if i.val < 24 then (57, 173) else (81, 224)))) else (if i.val < 27 then (if i.val < 26 then (105, 250) else (3, 132)) else (if i.val < 28 then (103, 71) else (if i.val < 29 then (114, 33) else (122, 13))))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then (25, 125) else (138, 254)) else (if i.val < 33 then (7, 123) else (if i.val < 34 then (111, 11) else (138, 82)))) else (if i.val < 37 then (if i.val < 36 then (141, 77) else (141, 237)) else (if i.val < 38 then (118, 203) else (if i.val < 39 then (103, 64) else (73, 40))))))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then (121, 81) else (33, 244)) else (if i.val < 43 then (134, 144) else (if i.val < 44 then (109, 123) else (120, 141)))) else (if i.val < 47 then (if i.val < 46 then (11, 253) else (132, 6)) else (if i.val < 48 then (142, 253) else (if i.val < 49 then (111, 174) else (0, 37))))) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then (56, 59) else (28, 10)) else (if i.val < 53 then (132, 152) else (if i.val < 54 then (25, 76) else (144, 154)))) else (if i.val < 57 then (if i.val < 56 then (37, 177) else (130, 157)) else (if i.val < 58 then (71, 178) else (if i.val < 59 then (121, 106) else (66, 68)))))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then (118, 3) else (128, 199)) else (if i.val < 63 then (80, 43) else (if i.val < 64 then (130, 112) else (143, 240)))) else (if i.val < 67 then (if i.val < 66 then (137, 65) else (43, 64)) else (if i.val < 68 then (66, 54) else (if i.val < 69 then (92, 20) else (132, 187))))) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then (129, 90) else (33, 68)) else (if i.val < 73 then (90, 161) else (if i.val < 74 then (134, 94) else (139, 181)))) else (if i.val < 78 then (if i.val < 76 then (138, 129) else (if i.val < 77 then (143, 215) else (132, 237))) else (if i.val < 79 then (22, 101) else (if i.val < 80 then (142, 8) else (112, 161)))))))) else (if i.val < 121 then (if i.val < 101 then (if i.val < 91 then (if i.val < 86 then (if i.val < 83 then (if i.val < 82 then (123, 199) else (117, 213)) else (if i.val < 84 then (11, 29) else (if i.val < 85 then (112, 171) else (103, 38)))) else (if i.val < 88 then (if i.val < 87 then (133, 254) else (9, 23)) else (if i.val < 89 then (143, 241) else (if i.val < 90 then (29, 48) else (129, 23))))) else (if i.val < 96 then (if i.val < 93 then (if i.val < 92 then (40, 102) else (102, 225)) else (if i.val < 94 then (106, 131) else (if i.val < 95 then (61, 76) else (73, 150)))) else (if i.val < 98 then (if i.val < 97 then (69, 214) else (0, 97)) else (if i.val < 99 then (142, 220) else (if i.val < 100 then (84, 33) else (100, 251)))))) else (if i.val < 111 then (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then (44, 237) else (132, 32)) else (if i.val < 104 then (81, 68) else (if i.val < 105 then (140, 122) else (144, 97)))) else (if i.val < 108 then (if i.val < 107 then (45, 86) else (26, 93)) else (if i.val < 109 then (83, 223) else (if i.val < 110 then (117, 76) else (108, 88))))) else (if i.val < 116 then (if i.val < 113 then (if i.val < 112 then (140, 159) else (44, 86)) else (if i.val < 114 then (140, 154) else (if i.val < 115 then (117, 220) else (144, 49)))) else (if i.val < 118 then (if i.val < 117 then (20, 200) else (126, 154)) else (if i.val < 119 then (70, 27) else (if i.val < 120 then (83, 161) else (43, 182))))))) else (if i.val < 141 then (if i.val < 131 then (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then (118, 163) else (134, 217)) else (if i.val < 124 then (136, 109) else (if i.val < 125 then (45, 234) else (135, 184)))) else (if i.val < 128 then (if i.val < 127 then (112, 207) else (109, 102)) else (if i.val < 129 then (27, 36) else (if i.val < 130 then (77, 79) else (15, 167))))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 132 then (55, 213) else (68, 175)) else (if i.val < 134 then (129, 213) else (if i.val < 135 then (118, 55) else (61, 0)))) else (if i.val < 138 then (if i.val < 137 then (115, 49) else (63, 122)) else (if i.val < 139 then (110, 48) else (if i.val < 140 then (101, 202) else (143, 183)))))) else (if i.val < 151 then (if i.val < 146 then (if i.val < 143 then (if i.val < 142 then (143, 8) else (95, 151)) else (if i.val < 144 then (112, 170) else (if i.val < 145 then (112, 252) else (119, 146)))) else (if i.val < 148 then (if i.val < 147 then (107, 89) else (89, 35)) else (if i.val < 149 then (27, 168) else (if i.val < 150 then (60, 168) else (117, 91))))) else (if i.val < 156 then (if i.val < 153 then (if i.val < 152 then (96, 163) else (144, 102)) else (if i.val < 154 then (127, 29) else (if i.val < 155 then (116, 181) else (103, 219)))) else (if i.val < 159 then (if i.val < 157 then (134, 238) else (if i.val < 158 then (79, 255) else (9, 203))) else (if i.val < 160 then (137, 24) else (if i.val < 161 then (137, 205) else (131, 38))))))))) else (if i.val < 243 then (if i.val < 202 then (if i.val < 182 then (if i.val < 172 then (if i.val < 167 then (if i.val < 164 then (if i.val < 163 then (128, 240) else (95, 148)) else (if i.val < 165 then (141, 38) else (if i.val < 166 then (142, 117) else (78, 185)))) else (if i.val < 169 then (if i.val < 168 then (36, 63) else (135, 233)) else (if i.val < 170 then (38, 174) else (if i.val < 171 then (139, 85) else (77, 133))))) else (if i.val < 177 then (if i.val < 174 then (if i.val < 173 then (143, 131) else (88, 86)) else (if i.val < 175 then (144, 210) else (if i.val < 176 then (54, 39) else (86, 109)))) else (if i.val < 179 then (if i.val < 178 then (60, 240) else (71, 174)) else (if i.val < 180 then (138, 130) else (if i.val < 181 then (58, 208) else (31, 190)))))) else (if i.val < 192 then (if i.val < 187 then (if i.val < 184 then (if i.val < 183 then (94, 64) else (96, 172)) else (if i.val < 185 then (101, 77) else (if i.val < 186 then (22, 25) else (81, 195)))) else (if i.val < 189 then (if i.val < 188 then (62, 66) else (139, 169)) else (if i.val < 190 then (103, 82) else (if i.val < 191 then (142, 70) else (132, 175))))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 193 then (124, 85) else (56, 124)) else (if i.val < 195 then (2, 130) else (if i.val < 196 then (80, 186) else (114, 65)))) else (if i.val < 199 then (if i.val < 198 then (68, 170) else (66, 78)) else (if i.val < 200 then (14, 212) else (if i.val < 201 then (126, 147) else (139, 166))))))) else (if i.val < 222 then (if i.val < 212 then (if i.val < 207 then (if i.val < 204 then (if i.val < 203 then (133, 77) else (99, 64)) else (if i.val < 205 then (111, 236) else (if i.val < 206 then (118, 160) else (11, 27)))) else (if i.val < 209 then (if i.val < 208 then (142, 132) else (139, 123)) else (if i.val < 210 then (133, 229) else (if i.val < 211 then (45, 208) else (121, 49))))) else (if i.val < 217 then (if i.val < 214 then (if i.val < 213 then (47, 208) else (41, 94)) else (if i.val < 215 then (128, 226) else (if i.val < 216 then (41, 221) else (107, 212)))) else (if i.val < 219 then (if i.val < 218 then (16, 64) else (21, 209)) else (if i.val < 220 then (126, 68) else (if i.val < 221 then (115, 147) else (139, 170)))))) else (if i.val < 232 then (if i.val < 227 then (if i.val < 224 then (if i.val < 223 then (39, 229) else (14, 86)) else (if i.val < 225 then (125, 151) else (if i.val < 226 then (116, 163) else (106, 162)))) else (if i.val < 229 then (if i.val < 228 then (56, 132) else (104, 62)) else (if i.val < 230 then (115, 91) else (if i.val < 231 then (17, 191) else (43, 168))))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 233 then (137, 93) else (56, 143)) else (if i.val < 235 then (92, 134) else (if i.val < 236 then (14, 213) else (106, 12)))) else (if i.val < 240 then (if i.val < 238 then (76, 149) else (if i.val < 239 then (134, 107) else (43, 83))) else (if i.val < 241 then (144, 64) else (if i.val < 242 then (133, 182) else (105, 84)))))))) else (if i.val < 283 then (if i.val < 263 then (if i.val < 253 then (if i.val < 248 then (if i.val < 245 then (if i.val < 244 then (143, 146) else (47, 7)) else (if i.val < 246 then (74, 233) else (if i.val < 247 then (107, 137) else (117, 187)))) else (if i.val < 250 then (if i.val < 249 then (8, 254) else (133, 67)) else (if i.val < 251 then (139, 163) else (if i.val < 252 then (48, 106) else (144, 73))))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 254 then (104, 186) else (70, 117)) else (if i.val < 256 then (137, 176) else (if i.val < 257 then (35, 67) else (139, 142)))) else (if i.val < 260 then (if i.val < 259 then (78, 227) else (126, 30)) else (if i.val < 261 then (134, 60) else (if i.val < 262 then (83, 251) else (123, 240)))))) else (if i.val < 273 then (if i.val < 268 then (if i.val < 265 then (if i.val < 264 then (84, 157) else (139, 233)) else (if i.val < 266 then (102, 251) else (if i.val < 267 then (128, 61) else (99, 101)))) else (if i.val < 270 then (if i.val < 269 then (43, 145) else (121, 240)) else (if i.val < 271 then (141, 35) else (if i.val < 272 then (132, 55) else (117, 224))))) else (if i.val < 278 then (if i.val < 275 then (if i.val < 274 then (134, 65) else (19, 128)) else (if i.val < 276 then (144, 27) else (if i.val < 277 then (62, 202) else (71, 72)))) else (if i.val < 280 then (if i.val < 279 then (121, 123) else (46, 0)) else (if i.val < 281 then (126, 204) else (if i.val < 282 then (127, 169) else (126, 211))))))) else (if i.val < 303 then (if i.val < 293 then (if i.val < 288 then (if i.val < 285 then (if i.val < 284 then (16, 177) else (55, 151)) else (if i.val < 286 then (143, 144) else (if i.val < 287 then (143, 229) else (59, 179)))) else (if i.val < 290 then (if i.val < 289 then (141, 67) else (141, 2)) else (if i.val < 291 then (128, 223) else (if i.val < 292 then (32, 39) else (17, 95))))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 294 then (26, 118) else (113, 180)) else (if i.val < 296 then (52, 202) else (if i.val < 297 then (135, 93) else (92, 113)))) else (if i.val < 300 then (if i.val < 299 then (11, 75) else (40, 88)) else (if i.val < 301 then (144, 151) else (if i.val < 302 then (119, 106) else (62, 109)))))) else (if i.val < 313 then (if i.val < 308 then (if i.val < 305 then (if i.val < 304 then (31, 130) else (9, 50)) else (if i.val < 306 then (141, 55) else (if i.val < 307 then (128, 138) else (135, 246)))) else (if i.val < 310 then (if i.val < 309 then (88, 204) else (20, 14)) else (if i.val < 311 then (61, 4) else (if i.val < 312 then (114, 129) else (110, 105))))) else (if i.val < 318 then (if i.val < 315 then (if i.val < 314 then (137, 81) else (120, 135)) else (if i.val < 316 then (81, 118) else (if i.val < 317 then (136, 95) else (53, 182)))) else (if i.val < 321 then (if i.val < 319 then (134, 197) else (if i.val < 320 then (129, 57) else (103, 124))) else (if i.val < 322 then (50, 170) else (if i.val < 323 then (50, 240) else (128, 77)))))))))) else (if i.val < 486 then (if i.val < 405 then (if i.val < 364 then (if i.val < 344 then (if i.val < 334 then (if i.val < 329 then (if i.val < 326 then (if i.val < 325 then (49, 225) else (79, 158)) else (if i.val < 327 then (61, 84) else (if i.val < 328 then (135, 91) else (13, 90)))) else (if i.val < 331 then (if i.val < 330 then (27, 128) else (43, 164)) else (if i.val < 332 then (143, 192) else (if i.val < 333 then (88, 122) else (143, 26))))) else (if i.val < 339 then (if i.val < 336 then (if i.val < 335 then (119, 178) else (109, 127)) else (if i.val < 337 then (51, 215) else (if i.val < 338 then (49, 59) else (49, 167)))) else (if i.val < 341 then (if i.val < 340 then (136, 132) else (31, 115)) else (if i.val < 342 then (1, 207) else (if i.val < 343 then (18, 251) else (142, 82)))))) else (if i.val < 354 then (if i.val < 349 then (if i.val < 346 then (if i.val < 345 then (72, 71) else (136, 10)) else (if i.val < 347 then (92, 38) else (if i.val < 348 then (61, 23) else (35, 236)))) else (if i.val < 351 then (if i.val < 350 then (31, 113) else (115, 3)) else (if i.val < 352 then (14, 187) else (if i.val < 353 then (57, 22) else (132, 104))))) else (if i.val < 359 then (if i.val < 356 then (if i.val < 355 then (100, 131) else (121, 40)) else (if i.val < 357 then (4, 252) else (if i.val < 358 then (51, 98) else (27, 30)))) else (if i.val < 361 then (if i.val < 360 then (130, 149) else (100, 36)) else (if i.val < 362 then (96, 233) else (if i.val < 363 then (5, 4) else (5, 18))))))) else (if i.val < 384 then (if i.val < 374 then (if i.val < 369 then (if i.val < 366 then (if i.val < 365 then (31, 106) else (100, 223)) else (if i.val < 367 then (144, 231) else (if i.val < 368 then (113, 225) else (65, 74)))) else (if i.val < 371 then (if i.val < 370 then (64, 167) else (143, 99)) else (if i.val < 372 then (14, 184) else (if i.val < 373 then (61, 155) else (27, 15))))) else (if i.val < 379 then (if i.val < 376 then (if i.val < 375 then (75, 174) else (71, 183)) else (if i.val < 377 then (87, 210) else (if i.val < 378 then (105, 27) else (14, 242)))) else (if i.val < 381 then (if i.val < 380 then (78, 249) else (137, 46)) else (if i.val < 382 then (59, 48) else (if i.val < 383 then (143, 231) else (141, 119)))))) else (if i.val < 394 then (if i.val < 389 then (if i.val < 386 then (if i.val < 385 then (143, 6) else (68, 18)) else (if i.val < 387 then (42, 13) else (if i.val < 388 then (89, 72) else (123, 248)))) else (if i.val < 391 then (if i.val < 390 then (136, 176) else (102, 68)) else (if i.val < 392 then (114, 78) else (if i.val < 393 then (141, 150) else (3, 3))))) else (if i.val < 399 then (if i.val < 396 then (if i.val < 395 then (23, 69) else (66, 132)) else (if i.val < 397 then (23, 62) else (if i.val < 398 then (132, 240) else (25, 10)))) else (if i.val < 402 then (if i.val < 400 then (100, 19) else (if i.val < 401 then (120, 171) else (40, 94))) else (if i.val < 403 then (67, 85) else (if i.val < 404 then (130, 224) else (124, 170)))))))) else (if i.val < 445 then (if i.val < 425 then (if i.val < 415 then (if i.val < 410 then (if i.val < 407 then (if i.val < 406 then (7, 188) else (44, 24)) else (if i.val < 408 then (143, 46) else (if i.val < 409 then (20, 254) else (53, 173)))) else (if i.val < 412 then (if i.val < 411 then (127, 154) else (104, 129)) else (if i.val < 413 then (122, 137) else (if i.val < 414 then (67, 100) else (134, 143))))) else (if i.val < 420 then (if i.val < 417 then (if i.val < 416 then (142, 248) else (96, 245)) else (if i.val < 418 then (144, 213) else (if i.val < 419 then (67, 8) else (11, 21)))) else (if i.val < 422 then (if i.val < 421 then (135, 195) else (92, 211)) else (if i.val < 423 then (23, 30) else (if i.val < 424 then (40, 195) else (125, 135)))))) else (if i.val < 435 then (if i.val < 430 then (if i.val < 427 then (if i.val < 426 then (35, 166) else (140, 59)) else (if i.val < 428 then (117, 99) else (if i.val < 429 then (41, 234) else (9, 211)))) else (if i.val < 432 then (if i.val < 431 then (39, 96) else (139, 13)) else (if i.val < 433 then (126, 74) else (if i.val < 434 then (140, 22) else (53, 162))))) else (if i.val < 440 then (if i.val < 437 then (if i.val < 436 then (60, 148) else (139, 103)) else (if i.val < 438 then (116, 9) else (if i.val < 439 then (129, 99) else (124, 200)))) else (if i.val < 442 then (if i.val < 441 then (79, 177) else (98, 20)) else (if i.val < 443 then (110, 131) else (if i.val < 444 then (17, 157) else (142, 138))))))) else (if i.val < 465 then (if i.val < 455 then (if i.val < 450 then (if i.val < 447 then (if i.val < 446 then (144, 30) else (138, 211)) else (if i.val < 448 then (79, 199) else (if i.val < 449 then (60, 106) else (103, 232)))) else (if i.val < 452 then (if i.val < 451 then (83, 197) else (56, 152)) else (if i.val < 453 then (135, 78) else (if i.val < 454 then (114, 192) else (144, 42))))) else (if i.val < 460 then (if i.val < 457 then (if i.val < 456 then (126, 189) else (125, 182)) else (if i.val < 458 then (78, 255) else (if i.val < 459 then (138, 232) else (44, 127)))) else (if i.val < 462 then (if i.val < 461 then (99, 20) else (55, 78)) else (if i.val < 463 then (71, 53) else (if i.val < 464 then (56, 8) else (99, 131)))))) else (if i.val < 475 then (if i.val < 470 then (if i.val < 467 then (if i.val < 466 then (139, 55) else (107, 1)) else (if i.val < 468 then (103, 129) else (if i.val < 469 then (14, 235) else (84, 16)))) else (if i.val < 472 then (if i.val < 471 then (1, 190) else (94, 18)) else (if i.val < 473 then (92, 194) else (if i.val < 474 then (108, 53) else (127, 232))))) else (if i.val < 480 then (if i.val < 477 then (if i.val < 476 then (102, 168) else (115, 85)) else (if i.val < 478 then (117, 2) else (if i.val < 479 then (123, 103) else (55, 211)))) else (if i.val < 483 then (if i.val < 481 then (126, 135) else (if i.val < 482 then (114, 234) else (79, 2))) else (if i.val < 484 then (83, 231) else (if i.val < 485 then (15, 23) else (31, 205))))))))) else (if i.val < 567 then (if i.val < 526 then (if i.val < 506 then (if i.val < 496 then (if i.val < 491 then (if i.val < 488 then (if i.val < 487 then (31, 201) else (81, 227)) else (if i.val < 489 then (88, 196) else (if i.val < 490 then (124, 180) else (72, 114)))) else (if i.val < 493 then (if i.val < 492 then (47, 119) else (45, 102)) else (if i.val < 494 then (5, 194) else (if i.val < 495 then (2, 9) else (143, 94))))) else (if i.val < 501 then (if i.val < 498 then (if i.val < 497 then (109, 85) else (136, 93)) else (if i.val < 499 then (12, 131) else (if i.val < 500 then (7, 177) else (5, 170)))) else (if i.val < 503 then (if i.val < 502 then (144, 117) else (86, 212)) else (if i.val < 504 then (59, 27) else (if i.val < 505 then (0, 98) else (45, 143)))))) else (if i.val < 516 then (if i.val < 511 then (if i.val < 508 then (if i.val < 507 then (33, 193) else (131, 251)) else (if i.val < 509 then (134, 219) else (if i.val < 510 then (142, 200) else (6, 86)))) else (if i.val < 513 then (if i.val < 512 then (55, 220) else (135, 115)) else (if i.val < 514 then (58, 224) else (if i.val < 515 then (17, 99) else (135, 161))))) else (if i.val < 521 then (if i.val < 518 then (if i.val < 517 then (144, 121) else (130, 17)) else (if i.val < 519 then (50, 18) else (if i.val < 520 then (107, 35) else (116, 85)))) else (if i.val < 523 then (if i.val < 522 then (107, 243) else (136, 134)) else (if i.val < 524 then (135, 248) else (if i.val < 525 then (140, 124) else (76, 181))))))) else (if i.val < 546 then (if i.val < 536 then (if i.val < 531 then (if i.val < 528 then (if i.val < 527 then (38, 4) else (143, 32)) else (if i.val < 529 then (26, 238) else (if i.val < 530 then (126, 54) else (6, 177)))) else (if i.val < 533 then (if i.val < 532 then (135, 193) else (36, 125)) else (if i.val < 534 then (62, 21) else (if i.val < 535 then (140, 82) else (45, 116))))) else (if i.val < 541 then (if i.val < 538 then (if i.val < 537 then (125, 245) else (38, 233)) else (if i.val < 539 then (50, 44) else (if i.val < 540 then (77, 188) else (124, 207)))) else (if i.val < 543 then (if i.val < 542 then (103, 83) else (49, 99)) else (if i.val < 544 then (133, 35) else (if i.val < 545 then (141, 167) else (125, 130)))))) else (if i.val < 556 then (if i.val < 551 then (if i.val < 548 then (if i.val < 547 then (139, 223) else (32, 135)) else (if i.val < 549 then (131, 56) else (if i.val < 550 then (1, 11) else (143, 177)))) else (if i.val < 553 then (if i.val < 552 then (101, 250) else (131, 31)) else (if i.val < 554 then (143, 251) else (if i.val < 555 then (133, 194) else (144, 187))))) else (if i.val < 561 then (if i.val < 558 then (if i.val < 557 then (136, 159) else (114, 138)) else (if i.val < 559 then (21, 194) else (if i.val < 560 then (33, 136) else (94, 22)))) else (if i.val < 564 then (if i.val < 562 then (120, 249) else (if i.val < 563 then (58, 174) else (121, 175))) else (if i.val < 565 then (114, 124) else (if i.val < 566 then (101, 53) else (123, 0)))))))) else (if i.val < 607 then (if i.val < 587 then (if i.val < 577 then (if i.val < 572 then (if i.val < 569 then (if i.val < 568 then (14, 37) else (141, 98)) else (if i.val < 570 then (138, 73) else (if i.val < 571 then (113, 43) else (141, 157)))) else (if i.val < 574 then (if i.val < 573 then (72, 230) else (142, 90)) else (if i.val < 575 then (92, 45) else (if i.val < 576 then (30, 140) else (22, 210))))) else (if i.val < 582 then (if i.val < 579 then (if i.val < 578 then (33, 80) else (39, 19)) else (if i.val < 580 then (132, 96) else (if i.val < 581 then (35, 11) else (43, 188)))) else (if i.val < 584 then (if i.val < 583 then (136, 206) else (2, 163)) else (if i.val < 585 then (14, 247) else (if i.val < 586 then (126, 22) else (138, 149)))))) else (if i.val < 597 then (if i.val < 592 then (if i.val < 589 then (if i.val < 588 then (39, 14) else (137, 76)) else (if i.val < 590 then (138, 132) else (if i.val < 591 then (1, 165) else (29, 185)))) else (if i.val < 594 then (if i.val < 593 then (82, 247) else (127, 9)) else (if i.val < 595 then (29, 157) else (if i.val < 596 then (67, 188) else (5, 83))))) else (if i.val < 602 then (if i.val < 599 then (if i.val < 598 then (10, 9) else (50, 118)) else (if i.val < 600 then (92, 167) else (if i.val < 601 then (142, 114) else (16, 11)))) else (if i.val < 604 then (if i.val < 603 then (141, 129) else (90, 195)) else (if i.val < 605 then (144, 33) else (if i.val < 606 then (70, 212) else (60, 48))))))) else (if i.val < 627 then (if i.val < 617 then (if i.val < 612 then (if i.val < 609 then (if i.val < 608 then (99, 221) else (137, 95)) else (if i.val < 610 then (143, 234) else (if i.val < 611 then (74, 172) else (25, 13)))) else (if i.val < 614 then (if i.val < 613 then (25, 150) else (111, 16)) else (if i.val < 615 then (43, 184) else (if i.val < 616 then (122, 247) else (59, 170))))) else (if i.val < 622 then (if i.val < 619 then (if i.val < 618 then (17, 77) else (129, 87)) else (if i.val < 620 then (82, 252) else (if i.val < 621 then (135, 234) else (131, 235)))) else (if i.val < 624 then (if i.val < 623 then (140, 172) else (143, 114)) else (if i.val < 625 then (142, 19) else (if i.val < 626 then (106, 134) else (134, 157)))))) else (if i.val < 637 then (if i.val < 632 then (if i.val < 629 then (if i.val < 628 then (95, 94) else (134, 163)) else (if i.val < 630 then (95, 58) else (if i.val < 631 then (80, 5) else (42, 203)))) else (if i.val < 634 then (if i.val < 633 then (135, 67) else (136, 56)) else (if i.val < 635 then (128, 106) else (if i.val < 636 then (32, 120) else (28, 29))))) else (if i.val < 642 then (if i.val < 639 then (if i.val < 638 then (135, 8) else (32, 139)) else (if i.val < 640 then (126, 82) else (if i.val < 641 then (119, 242) else (39, 126)))) else (if i.val < 645 then (if i.val < 643 then (143, 111) else (if i.val < 644 then (144, 205) else (142, 185))) else (if i.val < 646 then (140, 66) else (if i.val < 647 then (144, 94) else (144, 88)))))))))))

def g32p_supplierGroup23_classify : Fin 648 → Fin 102 :=
  fun i => (if i.val < 324 then (if i.val < 162 then (if i.val < 81 then (if i.val < 40 then (if i.val < 20 then (if i.val < 10 then (if i.val < 5 then (if i.val < 2 then (if i.val < 1 then 0 else 38) else (if i.val < 3 then 32 else (if i.val < 4 then 101 else 69))) else (if i.val < 7 then (if i.val < 6 then 57 else 57) else (if i.val < 8 then 57 else (if i.val < 9 then 45 else 84)))) else (if i.val < 15 then (if i.val < 12 then (if i.val < 11 then 96 else 38) else (if i.val < 13 then 30 else (if i.val < 14 then 34 else 30))) else (if i.val < 17 then (if i.val < 16 then 49 else 49) else (if i.val < 18 then 49 else (if i.val < 19 then 30 else 49))))) else (if i.val < 30 then (if i.val < 25 then (if i.val < 22 then (if i.val < 21 then 49 else 49) else (if i.val < 23 then 99 else (if i.val < 24 then 6 else 75))) else (if i.val < 27 then (if i.val < 26 then 57 else 57) else (if i.val < 28 then 57 else (if i.val < 29 then 46 else 46)))) else (if i.val < 35 then (if i.val < 32 then (if i.val < 31 then 13 else 57) else (if i.val < 33 then 13 else (if i.val < 34 then 46 else 46))) else (if i.val < 37 then (if i.val < 36 then 38 else 38) else (if i.val < 38 then 38 else (if i.val < 39 then 57 else 46)))))) else (if i.val < 60 then (if i.val < 50 then (if i.val < 45 then (if i.val < 42 then (if i.val < 41 then 46 else 13) else (if i.val < 43 then 38 else (if i.val < 44 then 38 else 38))) else (if i.val < 47 then (if i.val < 46 then 46 else 38) else (if i.val < 48 then 38 else (if i.val < 49 then 35 else 37)))) else (if i.val < 55 then (if i.val < 52 then (if i.val < 51 then 35 else 35) else (if i.val < 53 then 49 else (if i.val < 54 then 49 else 49))) else (if i.val < 57 then (if i.val < 56 then 35 else 49) else (if i.val < 58 then 49 else (if i.val < 59 then 49 else 69))))) else (if i.val < 70 then (if i.val < 65 then (if i.val < 62 then (if i.val < 61 then 21 else 21) else (if i.val < 63 then 35 else (if i.val < 64 then 49 else 49))) else (if i.val < 67 then (if i.val < 66 then 49 else 21) else (if i.val < 68 then 69 else (if i.val < 69 then 21 else 49)))) else (if i.val < 75 then (if i.val < 72 then (if i.val < 71 then 21 else 21) else (if i.val < 73 then 57 else (if i.val < 74 then 57 else 57))) else (if i.val < 78 then (if i.val < 76 then 49 else (if i.val < 77 then 49 else 49)) else (if i.val < 79 then 69 else (if i.val < 80 then 21 else 21))))))) else (if i.val < 121 then (if i.val < 101 then (if i.val < 91 then (if i.val < 86 then (if i.val < 83 then (if i.val < 82 then 49 else 21) else (if i.val < 84 then 69 else (if i.val < 85 then 21 else 57))) else (if i.val < 88 then (if i.val < 87 then 57 else 57) else (if i.val < 89 then 49 else (if i.val < 90 then 69 else 21)))) else (if i.val < 96 then (if i.val < 93 then (if i.val < 92 then 21 else 57) else (if i.val < 94 then 57 else (if i.val < 95 then 57 else 84))) else (if i.val < 98 then (if i.val < 97 then 45 else 97) else (if i.val < 99 then 57 else (if i.val < 100 then 84 else 45))))) else (if i.val < 111 then (if i.val < 106 then (if i.val < 103 then (if i.val < 102 then 84 else 38) else (if i.val < 104 then 38 else (if i.val < 105 then 38 else 57))) else (if i.val < 108 then (if i.val < 107 then 56 else 45) else (if i.val < 109 then 84 else (if i.val < 110 then 38 else 38)))) else (if i.val < 116 then (if i.val < 113 then (if i.val < 112 then 38 else 84) else (if i.val < 114 then 38 else (if i.val < 115 then 38 else 30))) else (if i.val < 118 then (if i.val < 117 then 34 else 30) else (if i.val < 119 then 84 else (if i.val < 120 then 45 else 56)))))) else (if i.val < 141 then (if i.val < 131 then (if i.val < 126 then (if i.val < 123 then (if i.val < 122 then 38 else 38) else (if i.val < 124 then 38 else (if i.val < 125 then 84 else 38))) else (if i.val < 128 then (if i.val < 127 then 38 else 38) else (if i.val < 129 then 30 else (if i.val < 130 then 30 else 34)))) else (if i.val < 136 then (if i.val < 133 then (if i.val < 132 then 84 else 38) else (if i.val < 134 then 38 else (if i.val < 135 then 38 else 34))) else (if i.val < 138 then (if i.val < 137 then 30 else 30) else (if i.val < 139 then 49 else (if i.val < 140 then 49 else 49))))) else (if i.val < 151 then (if i.val < 146 then (if i.val < 143 then (if i.val < 142 then 38 else 38) else (if i.val < 144 then 38 else (if i.val < 145 then 38 else 38))) else (if i.val < 148 then (if i.val < 147 then 38 else 30) else (if i.val < 149 then 34 else (if i.val < 150 then 30 else 38)))) else (if i.val < 156 then (if i.val < 153 then (if i.val < 152 then 38 else 38) else (if i.val < 154 then 30 else (if i.val < 155 then 30 else 34))) else (if i.val < 159 then (if i.val < 157 then 38 else (if i.val < 158 then 34 else 30)) else (if i.val < 160 then 49 else (if i.val < 161 then 49 else 49)))))))) else (if i.val < 243 then (if i.val < 202 then (if i.val < 182 then (if i.val < 172 then (if i.val < 167 then (if i.val < 164 then (if i.val < 163 then 38 else 38) else (if i.val < 165 then 38 else (if i.val < 166 then 30 else 34))) else (if i.val < 169 then (if i.val < 168 then 30 else 38) else (if i.val < 170 then 30 else (if i.val < 171 then 30 else 34)))) else (if i.val < 177 then (if i.val < 174 then (if i.val < 173 then 49 else 49) else (if i.val < 175 then 49 else (if i.val < 176 then 75 else 6))) else (if i.val < 179 then (if i.val < 178 then 30 else 49) else (if i.val < 180 then 49 else (if i.val < 181 then 49 else 76))))) else (if i.val < 192 then (if i.val < 187 then (if i.val < 184 then (if i.val < 183 then 75 else 6) else (if i.val < 185 then 49 else (if i.val < 186 then 67 else 75))) else (if i.val < 189 then (if i.val < 188 then 57 else 57) else (if i.val < 190 then 57 else (if i.val < 191 then 49 else 49)))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 193 then 49 else 78) else (if i.val < 195 then 24 else (if i.val < 196 then 6 else 49))) else (if i.val < 199 then (if i.val < 198 then 6 else 75) else (if i.val < 200 then 76 else (if i.val < 201 then 57 else 57)))))) else (if i.val < 222 then (if i.val < 212 then (if i.val < 207 then (if i.val < 204 then (if i.val < 203 then 57 else 49) else (if i.val < 205 then 78 else (if i.val < 206 then 75 else 67))) else (if i.val < 209 then (if i.val < 208 then 57 else 57) else (if i.val < 210 then 57 else (if i.val < 211 then 46 else 46)))) else (if i.val < 217 then (if i.val < 214 then (if i.val < 213 then 13 else 67) else (if i.val < 215 then 75 else (if i.val < 216 then 6 else 6))) else (if i.val < 219 then (if i.val < 218 then 24 else 78) else (if i.val < 220 then 57 else (if i.val < 221 then 57 else 57))))) else (if i.val < 232 then (if i.val < 227 then (if i.val < 224 then (if i.val < 223 then 6 else 75) else (if i.val < 225 then 57 else (if i.val < 226 then 57 else 57))) else (if i.val < 229 then (if i.val < 228 then 76 else 57) else (if i.val < 230 then 57 else (if i.val < 231 then 13 else 46)))) else (if i.val < 237 then (if i.val < 234 then (if i.val < 233 then 46 else 76) else (if i.val < 235 then 75 else (if i.val < 236 then 78 else 57))) else (if i.val < 240 then (if i.val < 238 then 57 else (if i.val < 239 then 57 else 67)) else (if i.val < 241 then 57 else (if i.val < 242 then 57 else 57))))))) else (if i.val < 283 then (if i.val < 263 then (if i.val < 253 then (if i.val < 248 then (if i.val < 245 then (if i.val < 244 then 46 else 13) else (if i.val < 246 then 46 else (if i.val < 247 then 38 else 38))) else (if i.val < 250 then (if i.val < 249 then 57 else 57) else (if i.val < 251 then 57 else (if i.val < 252 then 57 else 57)))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 254 then 57 else 46) else (if i.val < 256 then 46 else (if i.val < 257 then 13 else 57))) else (if i.val < 260 then (if i.val < 259 then 57 else 57) else (if i.val < 261 then 57 else (if i.val < 262 then 13 else 46))))) else (if i.val < 273 then (if i.val < 268 then (if i.val < 265 then (if i.val < 264 then 46 else 57) else (if i.val < 266 then 57 else (if i.val < 267 then 57 else 46))) else (if i.val < 270 then (if i.val < 269 then 13 else 46) else (if i.val < 271 then 38 else (if i.val < 272 then 38 else 38)))) else (if i.val < 278 then (if i.val < 275 then (if i.val < 274 then 57 else 57) else (if i.val < 276 then 57 else (if i.val < 277 then 57 else 46))) else (if i.val < 280 then (if i.val < 279 then 46 else 13) else (if i.val < 281 then 57 else (if i.val < 282 then 57 else 57)))))) else (if i.val < 303 then (if i.val < 293 then (if i.val < 288 then (if i.val < 285 then (if i.val < 284 then 13 else 46) else (if i.val < 286 then 46 else (if i.val < 287 then 46 else 13))) else (if i.val < 290 then (if i.val < 289 then 38 else 38) else (if i.val < 291 then 38 else (if i.val < 292 then 32 else 13)))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 294 then 46 else 46) else (if i.val < 296 then 38 else (if i.val < 297 then 38 else 38))) else (if i.val < 300 then (if i.val < 299 then 13 else 38) else (if i.val < 301 then 38 else (if i.val < 302 then 38 else 32))))) else (if i.val < 313 then (if i.val < 308 then (if i.val < 305 then (if i.val < 304 then 87 else 32) else (if i.val < 306 then 38 else (if i.val < 307 then 38 else 38))) else (if i.val < 310 then (if i.val < 309 then 32 else 2) else (if i.val < 311 then 32 else (if i.val < 312 then 49 else 49)))) else (if i.val < 318 then (if i.val < 315 then (if i.val < 314 then 49 else 38) else (if i.val < 316 then 38 else (if i.val < 317 then 38 else 38))) else (if i.val < 321 then (if i.val < 319 then 38 else (if i.val < 320 then 38 else 32)) else (if i.val < 322 then 4 else (if i.val < 323 then 92 else 38))))))))) else (if i.val < 486 then (if i.val < 405 then (if i.val < 364 then (if i.val < 344 then (if i.val < 334 then (if i.val < 329 then (if i.val < 326 then (if i.val < 325 then 88 else 35) else (if i.val < 327 then 32 else (if i.val < 328 then 38 else 92))) else (if i.val < 331 then (if i.val < 330 then 87 else 49) else (if i.val < 332 then 49 else (if i.val < 333 then 49 else 38)))) else (if i.val < 339 then (if i.val < 336 then (if i.val < 335 then 38 else 38) else (if i.val < 337 then 92 else (if i.val < 338 then 4 else 32))) else (if i.val < 341 then (if i.val < 340 then 38 else 93) else (if i.val < 342 then 2 else (if i.val < 343 then 32 else 49))))) else (if i.val < 354 then (if i.val < 349 then (if i.val < 346 then (if i.val < 345 then 49 else 21) else (if i.val < 347 then 21 else (if i.val < 348 then 32 else 2))) else (if i.val < 351 then (if i.val < 350 then 92 else 35) else (if i.val < 352 then 93 else (if i.val < 353 then 4 else 49)))) else (if i.val < 359 then (if i.val < 356 then (if i.val < 355 then 49 else 49) else (if i.val < 357 then 93 else (if i.val < 358 then 35 else 88))) else (if i.val < 361 then (if i.val < 360 then 49 else 49) else (if i.val < 362 then 49 else (if i.val < 363 then 88 else 87)))))) else (if i.val < 384 then (if i.val < 374 then (if i.val < 369 then (if i.val < 366 then (if i.val < 365 then 92 else 49) else (if i.val < 367 then 49 else (if i.val < 368 then 49 else 21))) else (if i.val < 371 then (if i.val < 370 then 69 else 21) else (if i.val < 372 then 87 else (if i.val < 373 then 32 else 88)))) else (if i.val < 379 then (if i.val < 376 then (if i.val < 375 then 4 else 49) else (if i.val < 377 then 49 else (if i.val < 378 then 92 else 2))) else (if i.val < 381 then (if i.val < 380 then 93 else 49) else (if i.val < 382 then 49 else (if i.val < 383 then 49 else 49))))) else (if i.val < 394 then (if i.val < 389 then (if i.val < 386 then (if i.val < 385 then 21 else 21) else (if i.val < 387 then 69 else (if i.val < 388 then 57 else 49))) else (if i.val < 391 then (if i.val < 390 then 49 else 49) else (if i.val < 392 then 49 else (if i.val < 393 then 49 else 49)))) else (if i.val < 399 then (if i.val < 396 then (if i.val < 395 then 69 else 21) else (if i.val < 397 then 21 else (if i.val < 398 then 49 else 49))) else (if i.val < 402 then (if i.val < 400 then 49 else (if i.val < 401 then 21 else 69)) else (if i.val < 403 then 21 else (if i.val < 404 then 49 else 49))))))) else (if i.val < 445 then (if i.val < 425 then (if i.val < 415 then (if i.val < 410 then (if i.val < 407 then (if i.val < 406 then 49 else 49) else (if i.val < 408 then 21 else (if i.val < 409 then 21 else 69))) else (if i.val < 412 then (if i.val < 411 then 57 else 57) else (if i.val < 413 then 49 else (if i.val < 414 then 69 else 21)))) else (if i.val < 420 then (if i.val < 417 then (if i.val < 416 then 21 else 49) else (if i.val < 418 then 49 else (if i.val < 419 then 21 else 69))) else (if i.val < 422 then (if i.val < 421 then 21 else 21) else (if i.val < 423 then 21 else (if i.val < 424 then 69 else 57))))) else (if i.val < 435 then (if i.val < 430 then (if i.val < 427 then (if i.val < 426 then 57 else 57) else (if i.val < 428 then 21 else (if i.val < 429 then 69 else 21))) else (if i.val < 432 then (if i.val < 431 then 69 else 57) else (if i.val < 433 then 57 else (if i.val < 434 then 57 else 69)))) else (if i.val < 440 then (if i.val < 437 then (if i.val < 436 then 57 else 57) else (if i.val < 438 then 57 else (if i.val < 439 then 21 else 57))) else (if i.val < 442 then (if i.val < 441 then 57 else 45) else (if i.val < 443 then 84 else (if i.val < 444 then 1 else 57)))))) else (if i.val < 465 then (if i.val < 455 then (if i.val < 450 then (if i.val < 447 then (if i.val < 446 then 57 else 57) else (if i.val < 448 then 57 else (if i.val < 449 then 57 else 57))) else (if i.val < 452 then (if i.val < 451 then 45 else 100) else (if i.val < 453 then 38 else (if i.val < 454 then 57 else 57)))) else (if i.val < 460 then (if i.val < 457 then (if i.val < 456 then 57 else 57) else (if i.val < 458 then 57 else (if i.val < 459 then 57 else 11))) else (if i.val < 462 then (if i.val < 461 then 84 else 11) else (if i.val < 463 then 45 else (if i.val < 464 then 98 else 45))))) else (if i.val < 475 then (if i.val < 470 then (if i.val < 467 then (if i.val < 466 then 57 else 57) else (if i.val < 468 then 57 else (if i.val < 469 then 1 else 56))) else (if i.val < 472 then (if i.val < 471 then 1 else 38) else (if i.val < 473 then 38 else (if i.val < 474 then 38 else 57)))) else (if i.val < 480 then (if i.val < 477 then (if i.val < 476 then 57 else 57) else (if i.val < 478 then 57 else (if i.val < 479 then 45 else 11))) else (if i.val < 483 then (if i.val < 481 then 57 else (if i.val < 482 then 57 else 57)) else (if i.val < 484 then 11 else (if i.val < 485 then 28 else 100)))))))) else (if i.val < 567 then (if i.val < 526 then (if i.val < 506 then (if i.val < 496 then (if i.val < 491 then (if i.val < 488 then (if i.val < 487 then 100 else 38) else (if i.val < 489 then 30 else (if i.val < 490 then 45 else 84))) else (if i.val < 493 then (if i.val < 492 then 11 else 56) else (if i.val < 494 then 100 else (if i.val < 495 then 28 else 38)))) else (if i.val < 501 then (if i.val < 498 then (if i.val < 497 then 38 else 38) else (if i.val < 499 then 45 else (if i.val < 500 then 28 else 98))) else (if i.val < 503 then (if i.val < 502 then 38 else 38) else (if i.val < 504 then 11 else (if i.val < 505 then 98 else 56))))) else (if i.val < 516 then (if i.val < 511 then (if i.val < 508 then (if i.val < 507 then 1 else 38) else (if i.val < 509 then 38 else (if i.val < 510 then 30 else 34))) else (if i.val < 513 then (if i.val < 512 then 98 else 38) else (if i.val < 514 then 56 else (if i.val < 515 then 28 else 38)))) else (if i.val < 521 then (if i.val < 518 then (if i.val < 517 then 38 else 38) else (if i.val < 519 then 34 else (if i.val < 520 then 30 else 30))) else (if i.val < 523 then (if i.val < 522 then 38 else 38) else (if i.val < 524 then 38 else (if i.val < 525 then 38 else 34)))))) else (if i.val < 546 then (if i.val < 536 then (if i.val < 531 then (if i.val < 528 then (if i.val < 527 then 30 else 38) else (if i.val < 529 then 30 else (if i.val < 530 then 30 else 34))) else (if i.val < 533 then (if i.val < 532 then 38 else 34) else (if i.val < 534 then 30 else (if i.val < 535 then 30 else 49)))) else (if i.val < 541 then (if i.val < 538 then (if i.val < 537 then 30 else 34) else (if i.val < 539 then 30 else (if i.val < 540 then 30 else 30))) else (if i.val < 543 then (if i.val < 542 then 34 else 34) else (if i.val < 544 then 30 else (if i.val < 545 then 49 else 30))))) else (if i.val < 556 then (if i.val < 551 then (if i.val < 548 then (if i.val < 547 then 30 else 34) else (if i.val < 549 then 49 else (if i.val < 550 then 49 else 49))) else (if i.val < 553 then (if i.val < 552 then 49 else 49) else (if i.val < 554 then 49 else (if i.val < 555 then 30 else 49)))) else (if i.val < 561 then (if i.val < 558 then (if i.val < 557 then 49 else 49) else (if i.val < 559 then 44 else (if i.val < 560 then 6 else 75))) else (if i.val < 564 then (if i.val < 562 then 49 else (if i.val < 563 then 49 else 49)) else (if i.val < 565 then 49 else (if i.val < 566 then 49 else 49))))))) else (if i.val < 607 then (if i.val < 587 then (if i.val < 577 then (if i.val < 572 then (if i.val < 569 then (if i.val < 568 then 95 else 49) else (if i.val < 570 then 49 else (if i.val < 571 then 49 else 49))) else (if i.val < 574 then (if i.val < 573 then 49 else 49) else (if i.val < 575 then 24 else (if i.val < 576 then 78 else 75)))) else (if i.val < 582 then (if i.val < 579 then (if i.val < 578 then 6 else 44) else (if i.val < 580 then 49 else (if i.val < 581 then 49 else 49))) else (if i.val < 584 then (if i.val < 583 then 49 else 44) else (if i.val < 585 then 24 else (if i.val < 586 then 57 else 49))))) else (if i.val < 597 then (if i.val < 592 then (if i.val < 589 then (if i.val < 588 then 24 else 49) else (if i.val < 590 then 49 else (if i.val < 591 then 95 else 95))) else (if i.val < 594 then (if i.val < 593 then 75 else 57) else (if i.val < 595 then 95 else (if i.val < 596 then 6 else 78)))) else (if i.val < 602 then (if i.val < 599 then (if i.val < 598 then 24 else 57) else (if i.val < 600 then 6 else (if i.val < 601 then 57 else 44))) else (if i.val < 604 then (if i.val < 603 then 46 else 57) else (if i.val < 605 then 57 else (if i.val < 606 then 46 else 13)))))) else (if i.val < 627 then (if i.val < 617 then (if i.val < 612 then (if i.val < 609 then (if i.val < 608 then 46 else 46) else (if i.val < 610 then 46 else (if i.val < 611 then 13 else 46))) else (if i.val < 614 then (if i.val < 613 then 13 else 13) else (if i.val < 615 then 46 else (if i.val < 616 then 46 else 46)))) else (if i.val < 622 then (if i.val < 619 then (if i.val < 618 then 46 else 38) else (if i.val < 620 then 38 else (if i.val < 621 then 38 else 38))) else (if i.val < 624 then (if i.val < 623 then 38 else 38) else (if i.val < 625 then 38 else (if i.val < 626 then 35 else 38))))) else (if i.val < 637 then (if i.val < 632 then (if i.val < 629 then (if i.val < 628 then 38 else 38) else (if i.val < 630 then 38 else (if i.val < 631 then 35 else 38))) else (if i.val < 634 then (if i.val < 633 then 38 else 38) else (if i.val < 635 then 38 else (if i.val < 636 then 4 else 35)))) else (if i.val < 642 then (if i.val < 639 then (if i.val < 638 then 38 else 4) else (if i.val < 640 then 35 else (if i.val < 641 then 21 else 69))) else (if i.val < 645 then (if i.val < 643 then 21 else (if i.val < 644 then 21 else 57)) else (if i.val < 646 then 57 else (if i.val < 647 then 57 else 57))))))))))

def g32p_supplierGroup23_support : Finset (Fin 102) :=
  {0, 1, 2, 4, 6, 11, 13, 21, 24, 28, 30, 32, 34, 35, 37, 38, 44, 45, 46, 49, 56, 57, 67, 69, 75, 76, 78, 84, 87, 88, 92, 93, 95, 96, 97, 98, 99, 100, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup23_matrix_000 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 0 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 0 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 0 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 0 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 0 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_001 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 1 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 1 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 1 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 1 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 1 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_002 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 2 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 2 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 2 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 2 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 2 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_003 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 3 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 3 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 3 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 3 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 3 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_004 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 4 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 4 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 4 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 4 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 4 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_005 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 5 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 5 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 5 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 5 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 5 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_006 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 6 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 6 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 6 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 6 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 6 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_007 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 7 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 7 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 7 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 7 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 7 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_008 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 8 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 8 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 8 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 8 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 8 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_009 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 9 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 9 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 9 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 9 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 9 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_010 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 10 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 10 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 10 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 10 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 10 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_011 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 11 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 11 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 11 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 11 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 11 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_012 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 12 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 12 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 12 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 12 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 12 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_013 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 13 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 13 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 13 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 13 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 13 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_014 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 14 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 14 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 14 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 14 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 14 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_015 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 15 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 15 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 15 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 15 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 15 r) ∈ g32p_supplierGroup23_support := by
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

theorem g32p_supplierGroup23_matrix_016 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 16 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 16 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 16 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 16 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 16 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_017 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 17 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 17 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 17 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 17 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 17 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_018 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 18 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 18 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 18 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 18 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 18 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_019 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 19 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 19 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 19 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 19 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 19 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_020 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 20 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 20 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 20 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 20 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 20 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_021 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 21 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 21 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 21 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 21 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 21 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_022 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 22 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 22 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 22 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 22 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 22 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_023 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 23 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 23 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 23 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 23 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 23 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_024 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 24 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 24 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 24 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_024 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 24 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 24 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 24 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_024 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 24 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_025 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 25 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 25 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 25 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_025 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 25 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 25 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 25 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_025 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 25 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_026 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 26 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 26 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 26 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_026 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 26 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 26 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 26 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_026 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 26 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_027 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 27 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 27 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 27 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_027 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 27 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 27 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 27 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_027 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 27 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_028 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 28 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 28 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 28 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_028 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 28 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 28 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 28 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_028 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 28 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_029 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 29 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 29 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 29 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_029 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 29 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 29 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 29 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_029 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 29 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_030 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 30 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 30 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 30 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_030 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 30 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 30 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 30 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_030 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 30 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

theorem g32p_supplierGroup23_matrix_031 : ∀ r : Fin 16,
    g32p_row32_groupNodes (g32p_finBlockIndex 648 31 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 31 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 31 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup23_class_031 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup23_source (g32p_finBlockIndex 648 31 r)).1 (g32p_supplierGroup23_source (g32p_finBlockIndex 648 31 r)).2 =
      g32p_supplierGroup23_classify (g32p_finBlockIndex 648 31 r) := by
  decide +kernel

theorem g32p_supplierGroup23_support_031 : ∀ r : Fin 16,
    g32p_supplierGroup23_classify (g32p_finBlockIndex 648 31 r) ∈ g32p_supplierGroup23_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
