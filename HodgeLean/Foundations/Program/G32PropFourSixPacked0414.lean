import HodgeLean.Foundations.Program.G32PropFourSixPacked0411
import HodgeLean.Foundations.Program.G32PropFourSixPacked0412
import HodgeLean.Foundations.Program.G32PropFourSixPacked0413
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow33
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def g32p_row32_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [15552])) else (if i.val < 4 then [] else (if i.val < 5 then [3888] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else [1296]))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [3888] else [])) else (if i.val < 36 then (if i.val < 35 then [5184] else [3888]) else (if i.val < 37 then [] else [155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [2592] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [15552] else [15552])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [3888] else (if i.val < 94 then [15552] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520])))))))

theorem g32p_row32_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup23_support) :
    g32p_supplierTracePolynomialCheck 648 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) c) (g32p_literalTraceValue 31 c)
      [1, 1, 1] (g32p_row32_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row32_tracePolynomial_000
  · exact g32p_row32_tracePolynomial_001
  · exact g32p_row32_tracePolynomial_002
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_004
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_006
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (18 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_021
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_028
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_030
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_034
  · exact g32p_row32_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_037
  · exact g32p_row32_tracePolynomial_038
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_044
  · exact g32p_row32_tracePolynomial_045
  · exact g32p_row32_tracePolynomial_046
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_049
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_056
  · exact g32p_row32_tracePolynomial_057
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_075
  · exact g32p_row32_tracePolynomial_076
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_078
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_087
  · exact g32p_row32_tracePolynomial_088
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_092
  · exact g32p_row32_tracePolynomial_093
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup23_support) hc)
  · exact g32p_row32_tracePolynomial_095
  · exact g32p_row32_tracePolynomial_096
  · exact g32p_row32_tracePolynomial_097
  · exact g32p_row32_tracePolynomial_098
  · exact g32p_row32_tracePolynomial_099
  · exact g32p_row32_tracePolynomial_100
  · exact g32p_row32_tracePolynomial_101

theorem g32p_row32_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 31 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 31 c) := by
  by_cases hc : c ∈ g32p_supplierGroup23_support
  · have hclass (j : Fin 648) :
        IsConj (g32p_literalRepresentative c) (g32p_row32_groupEquiv j : g32p_G) ↔
          g32p_row32_supplierClassifier j = c := by
      simpa only [g32p_row32_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row32_supplierClass_iff (g32p_row32_groupEquiv j) c
    have hχ (j : Fin 648) :
        (g32p_recordedSupplierCharacters 31 (g32p_row32_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row32_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 31 (show (g32p_recordedSuppliers 31).H from g32p_row32_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row32_characterValues (g32p_row32_groupEquiv.symm (g32p_row32_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 31).H (g32p_recordedSupplierCharacters 31)
      (g32p_literalRepresentative c) g32p_row32_groupEquiv g32p_row32_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row32_characterValues j)).val) c 3 648
      (g32p_literalCentralizer c) (g32p_literalTraceValue 31 c) [1, 1, 1]
      (g32p_row32_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row32_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 31)))
      (g32p_row32_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row32_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row32_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
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

theorem g32p_row32_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
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

theorem g32p_row32_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
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

theorem g32p_row32_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
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

theorem g32p_row32_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
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

theorem g32p_row32_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
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

theorem g32p_row32_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row32_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row32_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
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

theorem g32p_row32_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row32_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row32_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row32_variantArithmetic_00_0 r
  · exact g32p_row32_variantArithmetic_01_0 r
  · exact g32p_row32_variantArithmetic_02_0 r
  · exact g32p_row32_variantArithmetic_03_0 r
  · exact g32p_row32_variantArithmetic_04_0 r
  · exact g32p_row32_variantArithmetic_05_0 r
  · exact g32p_row32_variantArithmetic_06_0 r

theorem g32p_row32_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row32_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row32_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row32_variantArithmetic_00_1 r
  · exact g32p_row32_variantArithmetic_01_1 r
  · exact g32p_row32_variantArithmetic_02_1 r
  · exact g32p_row32_variantArithmetic_03_1 r
  · exact g32p_row32_variantArithmetic_04_1 r
  · exact g32p_row32_variantArithmetic_05_1 r
  · exact g32p_row32_variantArithmetic_06_1 r

theorem g32p_row32_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row32_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row32_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row32_variantArithmetic_00_2 r
  · exact g32p_row32_variantArithmetic_01_2 r
  · exact g32p_row32_variantArithmetic_02_2 r
  · exact g32p_row32_variantArithmetic_03_2 r
  · exact g32p_row32_variantArithmetic_04_2 r
  · exact g32p_row32_variantArithmetic_05_2 r
  · exact g32p_row32_variantArithmetic_06_2 r

theorem g32p_row32_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row32_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row32_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row32_variantArithmetic_00_3 r
  · exact g32p_row32_variantArithmetic_01_3 r
  · exact g32p_row32_variantArithmetic_02_3 r
  · exact g32p_row32_variantArithmetic_03_3 r
  · exact g32p_row32_variantArithmetic_04_3 r
  · exact g32p_row32_variantArithmetic_05_3 r
  · exact g32p_row32_variantArithmetic_06_3 r

theorem g32p_row32_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row32_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row32_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row32_variantArithmetic_00_4 r
  · exact g32p_row32_variantArithmetic_01_4 r
  · exact g32p_row32_variantArithmetic_02_4 r
  · exact g32p_row32_variantArithmetic_03_4 r
  · exact g32p_row32_variantArithmetic_04_4 r
  · exact g32p_row32_variantArithmetic_05_4 r
  · exact g32p_row32_variantArithmetic_06_4 r

theorem g32p_row32_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row32_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row32_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row32_variantArithmetic_00_5 r
  · exact g32p_row32_variantArithmetic_01_5 r
  · exact g32p_row32_variantArithmetic_02_5 r
  · exact g32p_row32_variantArithmetic_03_5 r
  · exact g32p_row32_variantArithmetic_04_5 r
  · exact g32p_row32_variantArithmetic_05_5 r
  · exact g32p_row32_variantArithmetic_06_5 r

theorem g32p_row32_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row32_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row32_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row32_variantArithmetic_00_6 r
  · exact g32p_row32_variantArithmetic_01_6 r
  · exact g32p_row32_variantArithmetic_02_6 r
  · exact g32p_row32_variantArithmetic_03_6 r
  · exact g32p_row32_variantArithmetic_04_6 r
  · exact g32p_row32_variantArithmetic_05_6 r
  · exact g32p_row32_variantArithmetic_06_6 r

theorem g32p_row32_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row32_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row32_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 31 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row32_variantArithmetic_00_7 r
  · exact g32p_row32_variantArithmetic_01_7 r
  · exact g32p_row32_variantArithmetic_02_7 r
  · exact g32p_row32_variantArithmetic_03_7 r
  · exact g32p_row32_variantArithmetic_04_7 r
  · exact g32p_row32_variantArithmetic_05_7 r
  · exact g32p_row32_variantArithmetic_06_7 r

theorem g32p_row32_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row32_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row32_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 31 c _ (g32p_row32_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row32_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 31 c _ (g32p_row32_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row32_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 31 c _ (g32p_row32_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row32_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 31 c _ (g32p_row32_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row32_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 31 c _ (g32p_row32_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row32_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 31 c _ (g32p_row32_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row32_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 31 c _ (g32p_row32_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row32_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 31 c _ (g32p_row32_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row32_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup24_source : Fin 432 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 216 then (if i.val < 108 then (if i.val < 54 then (if i.val < 27 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (107, 48) else (21, 117))) else (if i.val < 4 then (2, 20) else (if i.val < 5 then (25, 99) else (80, 106)))) else (if i.val < 9 then (if i.val < 7 then (54, 124) else (if i.val < 8 then (14, 196) else (30, 117))) else (if i.val < 11 then (if i.val < 10 then (56, 204) else (107, 240)) else (if i.val < 12 then (2, 80) else (16, 50))))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then (17, 229) else (if i.val < 15 then (89, 187) else (72, 172))) else (if i.val < 18 then (if i.val < 17 then (36, 183) else (66, 165)) else (if i.val < 19 then (37, 15) else (5, 194)))) else (if i.val < 23 then (if i.val < 21 then (27, 194) else (if i.val < 22 then (129, 178) else (50, 70))) else (if i.val < 25 then (if i.val < 24 then (0, 99) else (73, 61)) else (if i.val < 26 then (63, 38) else (93, 230)))))) else (if i.val < 40 then (if i.val < 33 then (if i.val < 30 then (if i.val < 28 then (14, 223) else (if i.val < 29 then (31, 203) else (0, 101))) else (if i.val < 31 then (42, 156) else (if i.val < 32 then (7, 237) else (68, 29)))) else (if i.val < 36 then (if i.val < 34 then (132, 186) else (if i.val < 35 then (15, 154) else (14, 235))) else (if i.val < 38 then (if i.val < 37 then (5, 113) else (47, 219)) else (if i.val < 39 then (142, 199) else (122, 249))))) else (if i.val < 47 then (if i.val < 43 then (if i.val < 41 then (9, 99) else (if i.val < 42 then (15, 227) else (131, 36))) else (if i.val < 45 then (if i.val < 44 then (142, 172) else (10, 87)) else (if i.val < 46 then (30, 73) else (11, 114)))) else (if i.val < 50 then (if i.val < 48 then (2, 91) else (if i.val < 49 then (93, 58) else (116, 98))) else (if i.val < 52 then (if i.val < 51 then (130, 215) else (19, 225)) else (if i.val < 53 then (86, 66) else (29, 153))))))) else (if i.val < 81 then (if i.val < 67 then (if i.val < 60 then (if i.val < 57 then (if i.val < 55 then (5, 167) else (if i.val < 56 then (12, 243) else (98, 241))) else (if i.val < 58 then (127, 250) else (if i.val < 59 then (43, 83) else (51, 56)))) else (if i.val < 63 then (if i.val < 61 then (5, 39) else (if i.val < 62 then (18, 75) else (85, 24))) else (if i.val < 65 then (if i.val < 64 then (30, 50) else (78, 149)) else (if i.val < 66 then (56, 123) else (114, 26))))) else (if i.val < 74 then (if i.val < 70 then (if i.val < 68 then (5, 143) else (if i.val < 69 then (19, 222) else (11, 51))) else (if i.val < 72 then (if i.val < 71 then (122, 186) else (54, 207)) else (if i.val < 73 then (25, 188) else (115, 207)))) else (if i.val < 77 then (if i.val < 75 then (86, 141) else (if i.val < 76 then (97, 174) else (32, 89))) else (if i.val < 79 then (if i.val < 78 then (15, 125) else (83, 187)) else (if i.val < 80 then (91, 212) else (131, 178)))))) else (if i.val < 94 then (if i.val < 87 then (if i.val < 84 then (if i.val < 82 then (129, 232) else (if i.val < 83 then (110, 69) else (37, 183))) else (if i.val < 85 then (38, 183) else (if i.val < 86 then (31, 230) else (113, 129)))) else (if i.val < 90 then (if i.val < 88 then (118, 241) else (if i.val < 89 then (136, 162) else (6, 62))) else (if i.val < 92 then (if i.val < 91 then (4, 155) else (25, 6)) else (if i.val < 93 then (97, 81) else (131, 207))))) else (if i.val < 101 then (if i.val < 97 then (if i.val < 95 then (70, 11) else (if i.val < 96 then (8, 138) else (57, 232))) else (if i.val < 99 then (if i.val < 98 then (87, 114) else (62, 120)) else (if i.val < 100 then (132, 46) else (95, 226)))) else (if i.val < 104 then (if i.val < 102 then (69, 235) else (if i.val < 103 then (6, 150) else (42, 58))) else (if i.val < 106 then (if i.val < 105 then (80, 54) else (121, 111)) else (if i.val < 107 then (21, 99) else (5, 192)))))))) else (if i.val < 162 then (if i.val < 135 then (if i.val < 121 then (if i.val < 114 then (if i.val < 111 then (if i.val < 109 then (13, 65) else (if i.val < 110 then (116, 108) else (120, 31))) else (if i.val < 112 then (136, 40) else (if i.val < 113 then (83, 163) else (55, 112)))) else (if i.val < 117 then (if i.val < 115 then (108, 93) else (if i.val < 116 then (10, 188) else (47, 109))) else (if i.val < 119 then (if i.val < 118 then (90, 20) else (11, 180)) else (if i.val < 120 then (20, 121) else (30, 40))))) else (if i.val < 128 then (if i.val < 124 then (if i.val < 122 then (49, 68) else (if i.val < 123 then (56, 151) else (85, 179))) else (if i.val < 126 then (if i.val < 125 then (80, 162) else (102, 58)) else (if i.val < 127 then (37, 46) else (66, 104)))) else (if i.val < 131 then (if i.val < 129 then (55, 48) else (if i.val < 130 then (30, 187) else (131, 74))) else (if i.val < 133 then (if i.val < 132 then (109, 62) else (32, 142)) else (if i.val < 134 then (108, 233) else (111, 75)))))) else (if i.val < 148 then (if i.val < 141 then (if i.val < 138 then (if i.val < 136 then (87, 157) else (if i.val < 137 then (51, 101) else (57, 159))) else (if i.val < 139 then (60, 180) else (if i.val < 140 then (122, 85) else (33, 13)))) else (if i.val < 144 then (if i.val < 142 then (57, 187) else (if i.val < 143 then (109, 158) else (123, 72))) else (if i.val < 146 then (if i.val < 145 then (27, 15) else (143, 62)) else (if i.val < 147 then (44, 239) else (62, 239))))) else (if i.val < 155 then (if i.val < 151 then (if i.val < 149 then (14, 92) else (if i.val < 150 then (83, 158) else (77, 75))) else (if i.val < 153 then (if i.val < 152 then (138, 175) else (135, 162)) else (if i.val < 154 then (126, 149) else (132, 76)))) else (if i.val < 158 then (if i.val < 156 then (15, 23) else (if i.val < 157 then (24, 69) else (125, 81))) else (if i.val < 160 then (if i.val < 159 then (115, 86) else (33, 14)) else (if i.val < 161 then (6, 197) else (5, 18))))))) else (if i.val < 189 then (if i.val < 175 then (if i.val < 168 then (if i.val < 165 then (if i.val < 163 then (101, 224) else (if i.val < 164 then (12, 188) else (92, 88))) else (if i.val < 166 then (87, 158) else (if i.val < 167 then (49, 210) else (138, 208)))) else (if i.val < 171 then (if i.val < 169 then (142, 0) else (if i.val < 170 then (3, 21) else (118, 245))) else (if i.val < 173 then (if i.val < 172 then (102, 48) else (7, 244)) else (if i.val < 174 then (17, 213) else (113, 72))))) else (if i.val < 182 then (if i.val < 178 then (if i.val < 176 then (0, 88) else (if i.val < 177 then (7, 199) else (125, 77))) else (if i.val < 180 then (if i.val < 179 then (120, 4) else (0, 167)) else (if i.val < 181 then (106, 24) else (143, 73)))) else (if i.val < 185 then (if i.val < 183 then (120, 3) else (if i.val < 184 then (26, 6) else (105, 107))) else (if i.val < 187 then (if i.val < 186 then (85, 244) else (47, 193)) else (if i.val < 188 then (28, 195) else (31, 111)))))) else (if i.val < 202 then (if i.val < 195 then (if i.val < 192 then (if i.val < 190 then (78, 131) else (if i.val < 191 then (93, 17) else (17, 118))) else (if i.val < 193 then (42, 127) else (if i.val < 194 then (100, 213) else (134, 55)))) else (if i.val < 198 then (if i.val < 196 then (17, 125) else (if i.val < 197 then (142, 61) else (0, 37))) else (if i.val < 200 then (if i.val < 199 then (23, 12) else (4, 175)) else (if i.val < 201 then (5, 73) else (36, 202))))) else (if i.val < 209 then (if i.val < 205 then (if i.val < 203 then (86, 202) else (if i.val < 204 then (93, 114) else (14, 160))) else (if i.val < 207 then (if i.val < 206 then (78, 209) else (25, 18)) else (if i.val < 208 then (29, 240) else (103, 139)))) else (if i.val < 212 then (if i.val < 210 then (15, 160) else (if i.val < 211 then (119, 240) else (5, 174))) else (if i.val < 214 then (if i.val < 213 then (128, 67) else (65, 85)) else (if i.val < 215 then (74, 244) else (120, 159))))))))) else (if i.val < 324 then (if i.val < 270 then (if i.val < 243 then (if i.val < 229 then (if i.val < 222 then (if i.val < 219 then (if i.val < 217 then (55, 220) else (if i.val < 218 then (96, 51) else (104, 30))) else (if i.val < 220 then (113, 138) else (if i.val < 221 then (80, 95) else (57, 161)))) else (if i.val < 225 then (if i.val < 223 then (25, 39) else (if i.val < 224 then (107, 62) else (5, 246))) else (if i.val < 227 then (if i.val < 226 then (82, 125) else (73, 44)) else (if i.val < 228 then (11, 232) else (79, 37))))) else (if i.val < 236 then (if i.val < 232 then (if i.val < 230 then (33, 146) else (if i.val < 231 then (79, 95) else (112, 145))) else (if i.val < 234 then (if i.val < 233 then (39, 113) else (22, 243)) else (if i.val < 235 then (46, 127) else (95, 141)))) else (if i.val < 239 then (if i.val < 237 then (47, 194) else (if i.val < 238 then (90, 7) else (5, 129))) else (if i.val < 241 then (if i.val < 240 then (43, 197) else (5, 25)) else (if i.val < 242 then (107, 51) else (107, 198)))))) else (if i.val < 256 then (if i.val < 249 then (if i.val < 246 then (if i.val < 244 then (34, 112) else (if i.val < 245 then (48, 12) else (5, 240))) else (if i.val < 247 then (34, 153) else (if i.val < 248 then (72, 165) else (133, 63)))) else (if i.val < 252 then (if i.val < 250 then (93, 157) else (if i.val < 251 then (14, 97) else (102, 87))) else (if i.val < 254 then (if i.val < 253 then (125, 189) else (5, 102)) else (if i.val < 255 then (39, 201) else (58, 255))))) else (if i.val < 263 then (if i.val < 259 then (if i.val < 257 then (111, 107) else (if i.val < 258 then (63, 215) else (33, 111))) else (if i.val < 261 then (if i.val < 260 then (90, 162) else (88, 169)) else (if i.val < 262 then (139, 151) else (32, 155)))) else (if i.val < 266 then (if i.val < 264 then (114, 122) else (if i.val < 265 then (115, 126) else (22, 125))) else (if i.val < 268 then (if i.val < 267 then (59, 160) else (29, 185)) else (if i.val < 269 then (8, 51) else (49, 227))))))) else (if i.val < 297 then (if i.val < 283 then (if i.val < 276 then (if i.val < 273 then (if i.val < 271 then (7, 126) else (if i.val < 272 then (14, 51) else (96, 36))) else (if i.val < 274 then (0, 96) else (if i.val < 275 then (125, 211) else (14, 210)))) else (if i.val < 279 then (if i.val < 277 then (114, 206) else (if i.val < 278 then (65, 204) else (26, 107))) else (if i.val < 281 then (if i.val < 280 then (56, 132) else (118, 77)) else (if i.val < 282 then (73, 38) else (9, 67))))) else (if i.val < 290 then (if i.val < 286 then (if i.val < 284 then (19, 118) else (if i.val < 285 then (2, 195) else (5, 254))) else (if i.val < 288 then (if i.val < 287 then (14, 242) else (139, 230)) else (if i.val < 289 then (7, 53) else (79, 184)))) else (if i.val < 293 then (if i.val < 291 then (132, 114) else (if i.val < 292 then (57, 122) else (99, 50))) else (if i.val < 295 then (if i.val < 294 then (78, 220) else (120, 17)) else (if i.val < 296 then (104, 121) else (16, 11)))))) else (if i.val < 310 then (if i.val < 303 then (if i.val < 300 then (if i.val < 298 then (15, 5) else (if i.val < 299 then (124, 51) else (14, 199))) else (if i.val < 301 then (59, 225) else (if i.val < 302 then (77, 90) else (134, 33)))) else (if i.val < 306 then (if i.val < 304 then (10, 36) else (if i.val < 305 then (124, 80) else (105, 150))) else (if i.val < 308 then (if i.val < 307 then (10, 104) else (132, 230)) else (if i.val < 309 then (76, 251) else (30, 42))))) else (if i.val < 317 then (if i.val < 313 then (if i.val < 311 then (116, 114) else (if i.val < 312 then (95, 87) else (100, 24))) else (if i.val < 315 then (if i.val < 314 then (77, 197) else (50, 241)) else (if i.val < 316 then (6, 195) else (86, 74)))) else (if i.val < 320 then (if i.val < 318 then (4, 144) else (if i.val < 319 then (133, 164) else (119, 82))) else (if i.val < 322 then (if i.val < 321 then (137, 219) else (28, 95)) else (if i.val < 323 then (95, 18) else (17, 80)))))))) else (if i.val < 378 then (if i.val < 351 then (if i.val < 337 then (if i.val < 330 then (if i.val < 327 then (if i.val < 325 then (89, 218) else (if i.val < 326 then (29, 178) else (128, 62))) else (if i.val < 328 then (81, 100) else (if i.val < 329 then (102, 52) else (52, 226)))) else (if i.val < 333 then (if i.val < 331 then (6, 63) else (if i.val < 332 then (71, 118) else (103, 122))) else (if i.val < 335 then (if i.val < 334 then (68, 246) else (67, 73)) else (if i.val < 336 then (131, 33) else (32, 141))))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then (53, 252) else (if i.val < 339 then (31, 115) else (123, 82))) else (if i.val < 342 then (if i.val < 341 then (66, 143) else (88, 174)) else (if i.val < 343 then (28, 204) else (86, 92)))) else (if i.val < 347 then (if i.val < 345 then (36, 151) else (if i.val < 346 then (40, 255) else (84, 206))) else (if i.val < 349 then (if i.val < 348 then (57, 102) else (25, 200)) else (if i.val < 350 then (80, 26) else (60, 230)))))) else (if i.val < 364 then (if i.val < 357 then (if i.val < 354 then (if i.val < 352 then (136, 67) else (if i.val < 353 then (6, 75) else (10, 83))) else (if i.val < 355 then (48, 68) else (if i.val < 356 then (100, 135) else (31, 170)))) else (if i.val < 360 then (if i.val < 358 then (107, 123) else (if i.val < 359 then (6, 27) else (24, 132))) else (if i.val < 362 then (if i.val < 361 then (80, 80) else (128, 104)) else (if i.val < 363 then (17, 219) else (4, 243))))) else (if i.val < 371 then (if i.val < 367 then (if i.val < 365 then (109, 218) else (if i.val < 366 then (87, 218) else (62, 201))) else (if i.val < 369 then (if i.val < 368 then (56, 88) else (92, 159)) else (if i.val < 370 then (35, 3) else (85, 143)))) else (if i.val < 374 then (if i.val < 372 then (62, 224) else (if i.val < 373 then (12, 228) else (132, 52))) else (if i.val < 376 then (if i.val < 375 then (113, 231) else (56, 57)) else (if i.val < 377 then (17, 232) else (54, 174))))))) else (if i.val < 405 then (if i.val < 391 then (if i.val < 384 then (if i.val < 381 then (if i.val < 379 then (88, 207) else (if i.val < 380 then (86, 197) else (100, 226))) else (if i.val < 382 then (125, 160) else (if i.val < 383 then (8, 48) else (135, 94)))) else (if i.val < 387 then (if i.val < 385 then (18, 246) else (if i.val < 386 then (53, 94) else (71, 3))) else (if i.val < 389 then (if i.val < 388 then (139, 173) else (113, 164)) else (if i.val < 390 then (106, 181) else (96, 11))))) else (if i.val < 398 then (if i.val < 394 then (if i.val < 392 then (119, 233) else (if i.val < 393 then (100, 218) else (105, 162))) else (if i.val < 396 then (if i.val < 395 then (130, 70) else (54, 139)) else (if i.val < 397 then (118, 113) else (120, 165)))) else (if i.val < 401 then (if i.val < 399 then (9, 25) else (if i.val < 400 then (25, 127) else (28, 170))) else (if i.val < 403 then (if i.val < 402 then (6, 134) else (67, 29)) else (if i.val < 404 then (124, 39) else (25, 141)))))) else (if i.val < 418 then (if i.val < 411 then (if i.val < 408 then (if i.val < 406 then (6, 73) else (if i.val < 407 then (130, 89) else (124, 87))) else (if i.val < 409 then (1, 155) else (if i.val < 410 then (115, 7) else (140, 184)))) else (if i.val < 414 then (if i.val < 412 then (123, 177) else (if i.val < 413 then (85, 215) else (128, 193))) else (if i.val < 416 then (if i.val < 415 then (101, 160) else (90, 130)) else (if i.val < 417 then (108, 14) else (87, 24))))) else (if i.val < 425 then (if i.val < 421 then (if i.val < 419 then (126, 10) else (if i.val < 420 then (9, 125) else (133, 173))) else (if i.val < 423 then (if i.val < 422 then (62, 63) else (115, 179)) else (if i.val < 424 then (0, 97) else (31, 80)))) else (if i.val < 428 then (if i.val < 426 then (115, 118) else (if i.val < 427 then (39, 159) else (70, 147))) else (if i.val < 430 then (if i.val < 429 then (122, 7) else (74, 9)) else (if i.val < 431 then (7, 174) else (6, 234))))))))))

def g32p_supplierGroup24_classify : Fin 432 → Fin 102 :=
  fun i => (if i.val < 216 then (if i.val < 108 then (if i.val < 54 then (if i.val < 27 then (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 90 else 24)) else (if i.val < 4 then 1 else (if i.val < 5 then 82 else 92))) else (if i.val < 9 then (if i.val < 7 then 77 else (if i.val < 8 then 92 else 78)) else (if i.val < 11 then (if i.val < 10 then 28 else 77) else (if i.val < 12 then 2 else 5)))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then 50 else (if i.val < 15 then 64 else 50)) else (if i.val < 18 then (if i.val < 17 then 59 else 72) else (if i.val < 19 then 64 else 100))) else (if i.val < 23 then (if i.val < 21 then 59 else (if i.val < 22 then 72 else 59)) else (if i.val < 25 then (if i.val < 24 then 99 else 45) else (if i.val < 26 then 32 else 72))))) else (if i.val < 40 then (if i.val < 33 then (if i.val < 30 then (if i.val < 28 then 100 else (if i.val < 29 then 100 else 101)) else (if i.val < 31 then 43 else (if i.val < 32 then 1 else 43))) else (if i.val < 36 then (if i.val < 34 then 25 else (if i.val < 35 then 3 else 1)) else (if i.val < 38 then (if i.val < 37 then 79 else 11) else (if i.val < 39 then 63 else 25)))) else (if i.val < 47 then (if i.val < 43 then (if i.val < 41 then 31 else (if i.val < 42 then 6 else 86)) else (if i.val < 45 then (if i.val < 44 then 63 else 67) else (if i.val < 46 then 79 else 11))) else (if i.val < 50 then (if i.val < 48 then 31 else (if i.val < 49 then 6 else 63)) else (if i.val < 52 then (if i.val < 51 then 86 else 31) else (if i.val < 53 then 6 else 78)))))) else (if i.val < 81 then (if i.val < 67 then (if i.val < 60 then (if i.val < 57 then (if i.val < 55 then 98 else (if i.val < 56 then 87 else 86)) else (if i.val < 58 then 63 else (if i.val < 59 then 67 else 90))) else (if i.val < 63 then (if i.val < 61 then 90 else (if i.val < 62 then 52 else 92)) else (if i.val < 65 then (if i.val < 64 then 76 else 92) else (if i.val < 66 then 78 else 27)))) else (if i.val < 74 then (if i.val < 70 then (if i.val < 68 then 76 else (if i.val < 69 then 3 else 78)) else (if i.val < 72 then (if i.val < 71 then 27 else 78) else (if i.val < 73 then 82 else 15))) else (if i.val < 77 then (if i.val < 75 then 40 else (if i.val < 76 then 27 else 3)) else (if i.val < 79 then (if i.val < 78 then 3 else 83) else (if i.val < 80 then 15 else 27))))) else (if i.val < 94 then (if i.val < 87 then (if i.val < 84 then (if i.val < 82 then 75 else (if i.val < 83 then 83 else 35)) else (if i.val < 85 then 4 else (if i.val < 86 then 19 else 48))) else (if i.val < 90 then (if i.val < 88 then 40 else (if i.val < 89 then 27 else 3)) else (if i.val < 92 then (if i.val < 91 then 52 else 52) else (if i.val < 93 then 83 else 15)))) else (if i.val < 101 then (if i.val < 97 then (if i.val < 95 then 83 else (if i.val < 96 then 4 else 19)) else (if i.val < 99 then (if i.val < 98 then 48 else 35) else (if i.val < 100 then 40 else 75))) else (if i.val < 104 then (if i.val < 102 then 83 else (if i.val < 103 then 4 else 19)) else (if i.val < 106 then (if i.val < 105 then 35 else 48) else (if i.val < 107 then 24 else 100))))))) else (if i.val < 162 then (if i.val < 135 then (if i.val < 121 then (if i.val < 114 then (if i.val < 111 then (if i.val < 109 then 93 else (if i.val < 110 then 15 else 75)) else (if i.val < 112 then 40 else (if i.val < 113 then 52 else 52))) else (if i.val < 117 then (if i.val < 115 then 77 else (if i.val < 116 then 18 else 56)) else (if i.val < 119 then (if i.val < 118 then 64 else 56) else (if i.val < 120 then 4 else 95)))) else (if i.val < 128 then (if i.val < 124 then (if i.val < 122 then 64 else (if i.val < 123 then 100 else 4)) else (if i.val < 126 then (if i.val < 125 then 94 else 86) else (if i.val < 127 then 32 else 72))) else (if i.val < 131 then (if i.val < 129 then 85 else (if i.val < 130 then 94 else 86)) else (if i.val < 133 then (if i.val < 132 then 72 else 32) else (if i.val < 134 then 94 else 86))))) else (if i.val < 148 then (if i.val < 141 then (if i.val < 138 then (if i.val < 136 then 50 else (if i.val < 137 then 91 else 19)) else (if i.val < 139 then 32 else (if i.val < 140 then 85 else 5))) else (if i.val < 144 then (if i.val < 142 then 5 else (if i.val < 143 then 94 else 50)) else (if i.val < 146 then (if i.val < 145 then 88 else 20) else (if i.val < 147 then 45 else 15)))) else (if i.val < 155 then (if i.val < 151 then (if i.val < 149 then 94 else (if i.val < 150 then 11 else 91)) else (if i.val < 153 then (if i.val < 152 then 86 else 20) else (if i.val < 154 then 59 else 7))) else (if i.val < 158 then (if i.val < 156 then 28 else (if i.val < 157 then 45 else 15)) else (if i.val < 160 then (if i.val < 159 then 15 else 5) else (if i.val < 161 then 5 else 87)))))) else (if i.val < 189 then (if i.val < 175 then (if i.val < 168 then (if i.val < 165 then (if i.val < 163 then 50 else (if i.val < 164 then 88 else 20)) else (if i.val < 166 then 11 else (if i.val < 167 then 91 else 59))) else (if i.val < 171 then (if i.val < 169 then 7 else (if i.val < 170 then 28 else 20)) else (if i.val < 173 then (if i.val < 172 then 45 else 56) else (if i.val < 174 then 50 else 50)))) else (if i.val < 182 then (if i.val < 178 then (if i.val < 176 then 88 else (if i.val < 177 then 11 else 59)) else (if i.val < 180 then (if i.val < 179 then 7 else 28) else (if i.val < 181 then 91 else 20))) else (if i.val < 185 then (if i.val < 183 then 20 else (if i.val < 184 then 84 else 35)) else (if i.val < 187 then (if i.val < 186 then 15 else 50) else (if i.val < 188 then 87 else 87))))) else (if i.val < 202 then (if i.val < 195 then (if i.val < 192 then (if i.val < 190 then 90 else (if i.val < 191 then 43 else 8)) else (if i.val < 193 then 43 else (if i.val < 194 then 25 else 63))) else (if i.val < 198 then (if i.val < 196 then 8 else (if i.val < 197 then 25 else 37)) else (if i.val < 200 then (if i.val < 199 then 6 else 84) else (if i.val < 201 then 67 else 31)))) else (if i.val < 209 then (if i.val < 205 then (if i.val < 203 then 40 else (if i.val < 204 then 43 else 98)) else (if i.val < 207 then (if i.val < 206 then 61 else 84) else (if i.val < 208 then 67 else 90))) else (if i.val < 212 then (if i.val < 210 then 31 else (if i.val < 211 then 43 else 98)) else (if i.val < 214 then (if i.val < 213 then 61 else 40) else (if i.val < 215 then 84 else 43)))))))) else (if i.val < 324 then (if i.val < 270 then (if i.val < 243 then (if i.val < 229 then (if i.val < 222 then (if i.val < 219 then (if i.val < 217 then 98 else (if i.val < 218 then 40 else 61)) else (if i.val < 220 then 25 else (if i.val < 221 then 89 else 23))) else (if i.val < 225 then (if i.val < 223 then 84 else (if i.val < 224 then 90 else 1)) else (if i.val < 227 then (if i.val < 226 then 78 else 81) else (if i.val < 228 then 56 else 58)))) else (if i.val < 236 then (if i.val < 232 then (if i.val < 230 then 23 else (if i.val < 231 then 61 else 40)) else (if i.val < 234 then (if i.val < 233 then 24 else 78) else (if i.val < 235 then 81 else 43))) else (if i.val < 239 then (if i.val < 237 then 25 else (if i.val < 238 then 58 else 95)) else (if i.val < 241 then (if i.val < 240 then 81 else 91) else (if i.val < 242 then 61 else 75))))) else (if i.val < 256 then (if i.val < 249 then (if i.val < 246 then (if i.val < 244 then 10 else (if i.val < 245 then 86 else 24)) else (if i.val < 247 then 8 else (if i.val < 248 then 56 else 58))) else (if i.val < 252 then (if i.val < 250 then 23 else (if i.val < 251 then 78 else 25)) else (if i.val < 254 then (if i.val < 253 then 58 else 95) else (if i.val < 255 then 75 else 10)))) else (if i.val < 263 then (if i.val < 259 then (if i.val < 257 then 81 else (if i.val < 258 then 61 else 24)) else (if i.val < 261 then (if i.val < 260 then 63 else 56) else (if i.val < 262 then 58 else 23))) else (if i.val < 266 then (if i.val < 264 then 25 else (if i.val < 265 then 58 else 75)) else (if i.val < 268 then (if i.val < 267 then 10 else 95) else (if i.val < 269 then 11 else 88)))))) else (if i.val < 297 then (if i.val < 283 then (if i.val < 276 then (if i.val < 273 then (if i.val < 271 then 8 else (if i.val < 272 then 79 else 79)) else (if i.val < 274 then 96 else (if i.val < 275 then 29 else 76))) else (if i.val < 279 then (if i.val < 277 then 29 else (if i.val < 278 then 74 else 85)) else (if i.val < 281 then (if i.val < 280 then 76 else 74) else (if i.val < 282 then 83 else 2)))) else (if i.val < 290 then (if i.val < 286 then (if i.val < 284 then 4 else (if i.val < 285 then 44 else 1)) else (if i.val < 288 then (if i.val < 287 then 2 else 29) else (if i.val < 289 then 44 else 35))) else (if i.val < 293 then (if i.val < 291 then 48 else (if i.val < 292 then 24 else 55)) else (if i.val < 295 then (if i.val < 294 then 89 else 75) else (if i.val < 296 then 29 else 44))))) else (if i.val < 310 then (if i.val < 303 then (if i.val < 300 then (if i.val < 298 then 24 else (if i.val < 299 then 55 else 89)) else (if i.val < 301 then 48 else (if i.val < 302 then 29 else 29))) else (if i.val < 306 then (if i.val < 304 then 24 else (if i.val < 305 then 55 else 89)) else (if i.val < 308 then (if i.val < 307 then 44 else 48) else (if i.val < 309 then 66 else 71)))) else (if i.val < 317 then (if i.val < 313 then (if i.val < 311 then 29 else (if i.val < 312 then 74 else 55)) else (if i.val < 315 then (if i.val < 314 then 93 else 66) else (if i.val < 316 then 6 else 19))) else (if i.val < 320 then (if i.val < 318 then 81 else (if i.val < 319 then 29 else 74)) else (if i.val < 322 then (if i.val < 321 then 55 else 93) else (if i.val < 323 then 74 else 51))))))) else (if i.val < 378 then (if i.val < 351 then (if i.val < 337 then (if i.val < 330 then (if i.val < 327 then (if i.val < 325 then 32 else (if i.val < 326 then 71 else 89)) else (if i.val < 328 then 74 else (if i.val < 329 then 80 else 77))) else (if i.val < 333 then (if i.val < 331 then 2 else (if i.val < 332 then 52 else 66)) else (if i.val < 335 then (if i.val < 334 then 6 else 74) else (if i.val < 336 then 55 else 32)))) else (if i.val < 344 then (if i.val < 340 then (if i.val < 338 then 71 else (if i.val < 339 then 93 else 80)) else (if i.val < 342 then (if i.val < 341 then 74 else 27) else (if i.val < 343 then 66 else 6))) else (if i.val < 347 then (if i.val < 345 then 32 else (if i.val < 346 then 71 else 80)) else (if i.val < 349 then (if i.val < 348 then 5 else 56) else (if i.val < 350 then 87 else 4))))) else (if i.val < 364 then (if i.val < 357 then (if i.val < 354 then (if i.val < 352 then 72 else (if i.val < 353 then 4 else 18)) else (if i.val < 355 then 85 else (if i.val < 356 then 85 else 92))) else (if i.val < 360 then (if i.val < 358 then 67 else (if i.val < 359 then 28 else 11)) else (if i.val < 362 then (if i.val < 361 then 92 else 7) else (if i.val < 363 then 51 else 88)))) else (if i.val < 371 then (if i.val < 367 then (if i.val < 365 then 76 else (if i.val < 366 then 10 else 35)) else (if i.val < 369 then (if i.val < 368 then 92 else 7) else (if i.val < 370 then 51 else 10))) else (if i.val < 374 then (if i.val < 372 then 35 else (if i.val < 373 then 92 else 7)) else (if i.val < 376 then (if i.val < 375 then 10 else 35) else (if i.val < 377 then 51 else 77)))))) else (if i.val < 405 then (if i.val < 391 then (if i.val < 384 then (if i.val < 381 then (if i.val < 379 then 59 else (if i.val < 380 then 23 else 84)) else (if i.val < 382 then 66 else (if i.val < 383 then 51 else 41))) else (if i.val < 387 then (if i.val < 385 then 59 else (if i.val < 386 then 79 else 84)) else (if i.val < 389 then (if i.val < 388 then 66 else 10) else (if i.val < 390 then 66 else 41)))) else (if i.val < 398 then (if i.val < 394 then (if i.val < 392 then 41 else (if i.val < 393 then 84 else 66)) else (if i.val < 396 then (if i.val < 395 then 41 else 94) else (if i.val < 397 then 41 else 41))) else (if i.val < 401 then (if i.val < 399 then 65 else (if i.val < 400 then 11 else 93)) else (if i.val < 403 then (if i.val < 402 then 31 else 75) else (if i.val < 404 then 45 else 56))))) else (if i.val < 418 then (if i.val < 411 then (if i.val < 408 then (if i.val < 406 then 2 else (if i.val < 407 then 71 else 45)) else (if i.val < 409 then 95 else (if i.val < 410 then 17 else 71))) else (if i.val < 414 then (if i.val < 412 then 45 else (if i.val < 413 then 17 else 71)) else (if i.val < 416 then (if i.val < 415 then 45 else 17) else (if i.val < 417 then 71 else 10)))) else (if i.val < 425 then (if i.val < 421 then (if i.val < 419 then 17 else (if i.val < 420 then 65 else 17)) else (if i.val < 423 then (if i.val < 422 then 64 else 17) else (if i.val < 424 then 97 else 98))) else (if i.val < 428 then (if i.val < 426 then 32 else (if i.val < 427 then 6 else 80)) else (if i.val < 430 then (if i.val < 429 then 80 else 80) else (if i.val < 431 then 8 else 44)))))))))

def g32p_supplierGroup24_support : Finset (Fin 102) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 15, 17, 18, 19, 20, 23, 24, 25, 27, 28, 29, 31, 32, 35, 37, 40, 41, 43, 44, 45, 48, 50, 51, 52, 55, 56, 58, 59, 61, 63, 64, 65, 66, 67, 71, 72, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup24_matrix_000 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 0 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 0 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 0 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 0 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 0 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_001 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 1 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 1 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 1 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 1 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 1 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_002 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 2 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 2 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 2 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 2 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 2 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_003 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 3 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 3 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 3 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 3 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 3 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_004 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 4 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 4 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 4 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 4 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 4 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_005 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 5 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 5 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 5 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 5 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 5 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_006 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 6 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 6 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 6 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 6 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 6 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_007 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 7 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 7 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 7 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 7 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 7 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_008 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 8 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 8 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 8 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 8 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 8 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_009 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 9 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 9 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 9 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 9 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 9 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_010 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 10 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 10 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 10 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 10 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 10 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_011 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 11 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 11 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 11 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 11 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 11 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_012 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 12 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 12 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 12 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 12 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 12 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_013 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 13 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 13 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 13 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 13 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 13 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_014 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 14 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 14 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 14 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 14 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 14 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_015 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 15 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 15 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 15 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 15 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 15 r) ∈ g32p_supplierGroup24_support := by
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

theorem g32p_supplierGroup24_matrix_016 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 16 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 16 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 16 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 16 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 16 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_017 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 17 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 17 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 17 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 17 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 17 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_018 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 18 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 18 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 18 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 18 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 18 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_019 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 19 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 19 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 19 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 19 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 19 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_020 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 20 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 20 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 20 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 20 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 20 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_021 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 21 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 21 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 21 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 21 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 21 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_022 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 22 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 22 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 22 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 22 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 22 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_023 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 23 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 23 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 23 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 23 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 23 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_024 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 24 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 24 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 24 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_024 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 24 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 24 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 24 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_024 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 24 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_025 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 25 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 25 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 25 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_025 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 25 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 25 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 25 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_025 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 25 r) ∈ g32p_supplierGroup24_support := by
  decide +kernel

theorem g32p_supplierGroup24_matrix_026 : ∀ r : Fin 16,
    g32p_row33_groupNodes (g32p_finBlockIndex 432 26 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 26 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 26 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup24_class_026 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup24_source (g32p_finBlockIndex 432 26 r)).1 (g32p_supplierGroup24_source (g32p_finBlockIndex 432 26 r)).2 =
      g32p_supplierGroup24_classify (g32p_finBlockIndex 432 26 r) := by
  decide +kernel

theorem g32p_supplierGroup24_support_026 : ∀ r : Fin 16,
    g32p_supplierGroup24_classify (g32p_finBlockIndex 432 26 r) ∈ g32p_supplierGroup24_support := by
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

theorem g32p_supplierGroup24_matrix (i : Fin 432) :
    g32p_row33_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source i).1 (g32p_supplierGroup24_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row33_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup24_source i).1 (g32p_supplierGroup24_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup24_matrix_000 r
  · exact g32p_supplierGroup24_matrix_001 r
  · exact g32p_supplierGroup24_matrix_002 r
  · exact g32p_supplierGroup24_matrix_003 r
  · exact g32p_supplierGroup24_matrix_004 r
  · exact g32p_supplierGroup24_matrix_005 r
  · exact g32p_supplierGroup24_matrix_006 r
  · exact g32p_supplierGroup24_matrix_007 r
  · exact g32p_supplierGroup24_matrix_008 r
  · exact g32p_supplierGroup24_matrix_009 r
  · exact g32p_supplierGroup24_matrix_010 r
  · exact g32p_supplierGroup24_matrix_011 r
  · exact g32p_supplierGroup24_matrix_012 r
  · exact g32p_supplierGroup24_matrix_013 r
  · exact g32p_supplierGroup24_matrix_014 r
  · exact g32p_supplierGroup24_matrix_015 r
  · exact g32p_supplierGroup24_matrix_016 r
  · exact g32p_supplierGroup24_matrix_017 r
  · exact g32p_supplierGroup24_matrix_018 r
  · exact g32p_supplierGroup24_matrix_019 r
  · exact g32p_supplierGroup24_matrix_020 r
  · exact g32p_supplierGroup24_matrix_021 r
  · exact g32p_supplierGroup24_matrix_022 r
  · exact g32p_supplierGroup24_matrix_023 r
  · exact g32p_supplierGroup24_matrix_024 r
  · exact g32p_supplierGroup24_matrix_025 r
  · exact g32p_supplierGroup24_matrix_026 r

theorem g32p_supplierGroup24_class (i : Fin 432) :
    g32p_supplierForest_classes (g32p_supplierGroup24_source i).1 (g32p_supplierGroup24_source i).2 =
      g32p_supplierGroup24_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup24_source i).1 (g32p_supplierGroup24_source i).2 =
      g32p_supplierGroup24_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup24_class_000 r
  · exact g32p_supplierGroup24_class_001 r
  · exact g32p_supplierGroup24_class_002 r
  · exact g32p_supplierGroup24_class_003 r
  · exact g32p_supplierGroup24_class_004 r
  · exact g32p_supplierGroup24_class_005 r
  · exact g32p_supplierGroup24_class_006 r
  · exact g32p_supplierGroup24_class_007 r
  · exact g32p_supplierGroup24_class_008 r
  · exact g32p_supplierGroup24_class_009 r
  · exact g32p_supplierGroup24_class_010 r
  · exact g32p_supplierGroup24_class_011 r
  · exact g32p_supplierGroup24_class_012 r
  · exact g32p_supplierGroup24_class_013 r
  · exact g32p_supplierGroup24_class_014 r
  · exact g32p_supplierGroup24_class_015 r
  · exact g32p_supplierGroup24_class_016 r
  · exact g32p_supplierGroup24_class_017 r
  · exact g32p_supplierGroup24_class_018 r
  · exact g32p_supplierGroup24_class_019 r
  · exact g32p_supplierGroup24_class_020 r
  · exact g32p_supplierGroup24_class_021 r
  · exact g32p_supplierGroup24_class_022 r
  · exact g32p_supplierGroup24_class_023 r
  · exact g32p_supplierGroup24_class_024 r
  · exact g32p_supplierGroup24_class_025 r
  · exact g32p_supplierGroup24_class_026 r

theorem g32p_supplierGroup24_support_mem (i : Fin 432) :
    g32p_supplierGroup24_classify i ∈ g32p_supplierGroup24_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup24_classify i ∈ g32p_supplierGroup24_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup24_support_000 r
  · exact g32p_supplierGroup24_support_001 r
  · exact g32p_supplierGroup24_support_002 r
  · exact g32p_supplierGroup24_support_003 r
  · exact g32p_supplierGroup24_support_004 r
  · exact g32p_supplierGroup24_support_005 r
  · exact g32p_supplierGroup24_support_006 r
  · exact g32p_supplierGroup24_support_007 r
  · exact g32p_supplierGroup24_support_008 r
  · exact g32p_supplierGroup24_support_009 r
  · exact g32p_supplierGroup24_support_010 r
  · exact g32p_supplierGroup24_support_011 r
  · exact g32p_supplierGroup24_support_012 r
  · exact g32p_supplierGroup24_support_013 r
  · exact g32p_supplierGroup24_support_014 r
  · exact g32p_supplierGroup24_support_015 r
  · exact g32p_supplierGroup24_support_016 r
  · exact g32p_supplierGroup24_support_017 r
  · exact g32p_supplierGroup24_support_018 r
  · exact g32p_supplierGroup24_support_019 r
  · exact g32p_supplierGroup24_support_020 r
  · exact g32p_supplierGroup24_support_021 r
  · exact g32p_supplierGroup24_support_022 r
  · exact g32p_supplierGroup24_support_023 r
  · exact g32p_supplierGroup24_support_024 r
  · exact g32p_supplierGroup24_support_025 r
  · exact g32p_supplierGroup24_support_026 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row33_supplierClassifier : Fin 432 → Fin 102 := g32p_supplierGroup24_classify

theorem g32p_row33_groupEquiv_isConj (i : Fin 432) :
    IsConj (g32p_row33_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row33_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup24_source i).1 (g32p_supplierGroup24_source i).2
  rw [g32p_supplierGroup24_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row33_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup24_matrix i)

def g32p_row33_supplierClass (h : (g32p_recordedSuppliers 32).H) : Fin 102 :=
  g32p_row33_supplierClassifier (g32p_row33_groupEquiv.symm h)

theorem g32p_row33_supplierClass_isConj (h : (g32p_recordedSuppliers 32).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row33_supplierClass h)) := by
  have he : (g32p_row33_groupEquiv (g32p_row33_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 32).H => (a : g32p_G))
      (g32p_row33_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row33_supplierClassifier (g32p_row33_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row33_groupEquiv_isConj (g32p_row33_groupEquiv.symm h)

theorem g32p_row33_supplierClass_iff (h : (g32p_recordedSuppliers 32).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row33_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row33_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row33_supplierClass_isConj h).symm

theorem g32p_row33_supplierClass_mem_support (h : (g32p_recordedSuppliers 32).H) :
    g32p_row33_supplierClass h ∈ g32p_supplierGroup24_support :=
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

theorem g32p_row33_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 0) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 0) (g32p_literalTraceValue 32 0)
      [1, 1, 1] [] = true := by
  rw [g32p_row33_traceCoefficients_000]
  decide +kernel

theorem g32p_row33_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 1 = [4, 1] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 1) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 1) (g32p_literalTraceValue 32 1)
      [1, 1, 1] [] = true := by
  rw [g32p_row33_traceCoefficients_001]
  decide +kernel

theorem g32p_row33_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 2 = [4, 0, 1] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 2) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 2) (g32p_literalTraceValue 32 2)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row33_traceCoefficients_002]
  decide +kernel

theorem g32p_row33_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 3 = [4, 0, 1] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 3) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 3) (g32p_literalTraceValue 32 3)
      [1, 1, 1] [432] = true := by
  rw [g32p_row33_traceCoefficients_003]
  decide +kernel

theorem g32p_row33_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 4 = [4, 4] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 4) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 4) (g32p_literalTraceValue 32 4)
      [1, 1, 1] [] = true := by
  rw [g32p_row33_traceCoefficients_004]
  decide +kernel

theorem g32p_row33_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 5 = [6] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 5) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 5) (g32p_literalTraceValue 32 5)
      [1, 1, 1] [] = true := by
  rw [g32p_row33_traceCoefficients_005]
  decide +kernel

theorem g32p_row33_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 6 = [0, 4, 4] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 6) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 6) (g32p_literalTraceValue 32 6)
      [1, 1, 1] [1296] = true := by
  rw [g32p_row33_traceCoefficients_006]
  decide +kernel

theorem g32p_row33_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 7 = [6] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 7) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 7) (g32p_literalTraceValue 32 7)
      [1, 1, 1] [] = true := by
  rw [g32p_row33_traceCoefficients_007]
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

theorem g32p_row33_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 8 = [4, 1] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 8) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 8) (g32p_literalTraceValue 32 8)
      [1, 1, 1] [] = true := by
  rw [g32p_row33_traceCoefficients_008]
  decide +kernel

theorem g32p_row33_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 10 = [4, 0, 4] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 10) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 10) (g32p_literalTraceValue 32 10)
      [1, 1, 1] [432] = true := by
  rw [g32p_row33_traceCoefficients_010]
  decide +kernel

theorem g32p_row33_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 11 = [4, 0, 4] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 11) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 11) (g32p_literalTraceValue 32 11)
      [1, 1, 1] [2592] = true := by
  rw [g32p_row33_traceCoefficients_011]
  decide +kernel

theorem g32p_row33_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 15 = [4, 4] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 15) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 15) (g32p_literalTraceValue 32 15)
      [1, 1, 1] [] = true := by
  rw [g32p_row33_traceCoefficients_015]
  decide +kernel

theorem g32p_row33_traceCoefficients_017 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 17 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_017 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 17) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 17) (g32p_literalTraceValue 32 17)
      [1, 1, 1] [432] = true := by
  rw [g32p_row33_traceCoefficients_017]
  decide +kernel

theorem g32p_row33_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 18 = [2] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 18) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 18) (g32p_literalTraceValue 32 18)
      [1, 1, 1] [] = true := by
  rw [g32p_row33_traceCoefficients_018]
  decide +kernel

theorem g32p_row33_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 19 = [1, 0, 4] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 19) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 19) (g32p_literalTraceValue 32 19)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row33_traceCoefficients_019]
  decide +kernel

theorem g32p_row33_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 20 = [6] := by
  decide +kernel

theorem g32p_row33_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer 20) 3
      (g32p_supplierTraceCoefficients g32p_row33_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row33_characterValues j)).val) 20) (g32p_literalTraceValue 32 20)
      [1, 1, 1] [] = true := by
  rw [g32p_row33_traceCoefficients_020]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
