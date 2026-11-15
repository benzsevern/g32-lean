import HodgeLean.Foundations.Program.G32PropFourSixPacked0417
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow36
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

def g32p_row35_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [3888] else [15552])) else (if i.val < 4 then [1728] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [1296] else (if i.val < 8 then [432] else [432])) else (if i.val < 10 then [] else (if i.val < 11 then [432] else [2592])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [432] else [2592]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [864] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [1728] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [432])) else (if i.val < 42 then [] else (if i.val < 43 then [] else [864]))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [1296] else [])) else (if i.val < 49 then (if i.val < 48 then [] else [432]) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else [2592]))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [1728] else [3456])) else (if i.val < 67 then [] else (if i.val < 68 then [3888] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [432])) else (if i.val < 74 then (if i.val < 73 then [432] else []) else (if i.val < 75 then [] else [1296]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [2592])) else (if i.val < 80 then [432] else (if i.val < 81 then [432] else [432]))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [1296])) else (if i.val < 87 then (if i.val < 86 then [] else [432]) else (if i.val < 88 then [15552] else [15552])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [1728] else (if i.val < 91 then [1728] else [1728])) else (if i.val < 93 then [] else (if i.val < 94 then [15552] else []))) else (if i.val < 98 then (if i.val < 96 then [3888] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [3888] else []) else (if i.val < 101 then [] else [155520])))))))

theorem g32p_row35_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup24_support) :
    g32p_supplierTracePolynomialCheck 432 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row35_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row35_characterValues j)).val) c) (g32p_literalTraceValue 34 c)
      [1, 1, 1] (g32p_row35_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row35_tracePolynomial_000
  · exact g32p_row35_tracePolynomial_001
  · exact g32p_row35_tracePolynomial_002
  · exact g32p_row35_tracePolynomial_003
  · exact g32p_row35_tracePolynomial_004
  · exact g32p_row35_tracePolynomial_005
  · exact g32p_row35_tracePolynomial_006
  · exact g32p_row35_tracePolynomial_007
  · exact g32p_row35_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_010
  · exact g32p_row35_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_017
  · exact g32p_row35_tracePolynomial_018
  · exact g32p_row35_tracePolynomial_019
  · exact g32p_row35_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_023
  · exact g32p_row35_tracePolynomial_024
  · exact g32p_row35_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_027
  · exact g32p_row35_tracePolynomial_028
  · exact g32p_row35_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_031
  · exact g32p_row35_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_040
  · exact g32p_row35_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_043
  · exact g32p_row35_tracePolynomial_044
  · exact g32p_row35_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_048
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_050
  · exact g32p_row35_tracePolynomial_051
  · exact g32p_row35_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_055
  · exact g32p_row35_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_058
  · exact g32p_row35_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_061
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_063
  · exact g32p_row35_tracePolynomial_064
  · exact g32p_row35_tracePolynomial_065
  · exact g32p_row35_tracePolynomial_066
  · exact g32p_row35_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_071
  · exact g32p_row35_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup24_support) hc)
  · exact g32p_row35_tracePolynomial_074
  · exact g32p_row35_tracePolynomial_075
  · exact g32p_row35_tracePolynomial_076
  · exact g32p_row35_tracePolynomial_077
  · exact g32p_row35_tracePolynomial_078
  · exact g32p_row35_tracePolynomial_079
  · exact g32p_row35_tracePolynomial_080
  · exact g32p_row35_tracePolynomial_081
  · exact g32p_row35_tracePolynomial_082
  · exact g32p_row35_tracePolynomial_083
  · exact g32p_row35_tracePolynomial_084
  · exact g32p_row35_tracePolynomial_085
  · exact g32p_row35_tracePolynomial_086
  · exact g32p_row35_tracePolynomial_087
  · exact g32p_row35_tracePolynomial_088
  · exact g32p_row35_tracePolynomial_089
  · exact g32p_row35_tracePolynomial_090
  · exact g32p_row35_tracePolynomial_091
  · exact g32p_row35_tracePolynomial_092
  · exact g32p_row35_tracePolynomial_093
  · exact g32p_row35_tracePolynomial_094
  · exact g32p_row35_tracePolynomial_095
  · exact g32p_row35_tracePolynomial_096
  · exact g32p_row35_tracePolynomial_097
  · exact g32p_row35_tracePolynomial_098
  · exact g32p_row35_tracePolynomial_099
  · exact g32p_row35_tracePolynomial_100
  · exact g32p_row35_tracePolynomial_101

theorem g32p_row35_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 34 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 34 c) := by
  by_cases hc : c ∈ g32p_supplierGroup24_support
  · have hclass (j : Fin 432) :
        IsConj (g32p_literalRepresentative c) (g32p_row33_groupEquiv j : g32p_G) ↔
          g32p_row35_supplierClassifier j = c := by
      simpa only [g32p_row35_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row35_supplierClass_iff (g32p_row33_groupEquiv j) c
    have hχ (j : Fin 432) :
        (g32p_recordedSupplierCharacters 34 (g32p_row33_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row35_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 34 (show (g32p_recordedSuppliers 34).H from g32p_row33_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row35_characterValues (g32p_row33_groupEquiv.symm (g32p_row33_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 34).H (g32p_recordedSupplierCharacters 34)
      (g32p_literalRepresentative c) g32p_row33_groupEquiv g32p_row35_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row35_characterValues j)).val) c 3 432
      (g32p_literalCentralizer c) (g32p_literalTraceValue 34 c) [1, 1, 1]
      (g32p_row35_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row35_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 34)))
      (g32p_row35_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row35_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row35_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
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

theorem g32p_row35_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
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

theorem g32p_row35_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
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

theorem g32p_row35_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
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

theorem g32p_row35_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
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

theorem g32p_row35_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
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

theorem g32p_row35_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row35_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row35_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
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

theorem g32p_row35_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row35_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row35_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row35_variantArithmetic_00_0 r
  · exact g32p_row35_variantArithmetic_01_0 r
  · exact g32p_row35_variantArithmetic_02_0 r
  · exact g32p_row35_variantArithmetic_03_0 r
  · exact g32p_row35_variantArithmetic_04_0 r
  · exact g32p_row35_variantArithmetic_05_0 r
  · exact g32p_row35_variantArithmetic_06_0 r

theorem g32p_row35_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row35_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row35_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row35_variantArithmetic_00_1 r
  · exact g32p_row35_variantArithmetic_01_1 r
  · exact g32p_row35_variantArithmetic_02_1 r
  · exact g32p_row35_variantArithmetic_03_1 r
  · exact g32p_row35_variantArithmetic_04_1 r
  · exact g32p_row35_variantArithmetic_05_1 r
  · exact g32p_row35_variantArithmetic_06_1 r

theorem g32p_row35_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row35_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row35_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row35_variantArithmetic_00_2 r
  · exact g32p_row35_variantArithmetic_01_2 r
  · exact g32p_row35_variantArithmetic_02_2 r
  · exact g32p_row35_variantArithmetic_03_2 r
  · exact g32p_row35_variantArithmetic_04_2 r
  · exact g32p_row35_variantArithmetic_05_2 r
  · exact g32p_row35_variantArithmetic_06_2 r

theorem g32p_row35_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row35_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row35_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row35_variantArithmetic_00_3 r
  · exact g32p_row35_variantArithmetic_01_3 r
  · exact g32p_row35_variantArithmetic_02_3 r
  · exact g32p_row35_variantArithmetic_03_3 r
  · exact g32p_row35_variantArithmetic_04_3 r
  · exact g32p_row35_variantArithmetic_05_3 r
  · exact g32p_row35_variantArithmetic_06_3 r

theorem g32p_row35_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row35_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row35_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row35_variantArithmetic_00_4 r
  · exact g32p_row35_variantArithmetic_01_4 r
  · exact g32p_row35_variantArithmetic_02_4 r
  · exact g32p_row35_variantArithmetic_03_4 r
  · exact g32p_row35_variantArithmetic_04_4 r
  · exact g32p_row35_variantArithmetic_05_4 r
  · exact g32p_row35_variantArithmetic_06_4 r

theorem g32p_row35_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row35_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row35_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row35_variantArithmetic_00_5 r
  · exact g32p_row35_variantArithmetic_01_5 r
  · exact g32p_row35_variantArithmetic_02_5 r
  · exact g32p_row35_variantArithmetic_03_5 r
  · exact g32p_row35_variantArithmetic_04_5 r
  · exact g32p_row35_variantArithmetic_05_5 r
  · exact g32p_row35_variantArithmetic_06_5 r

theorem g32p_row35_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row35_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row35_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row35_variantArithmetic_00_6 r
  · exact g32p_row35_variantArithmetic_01_6 r
  · exact g32p_row35_variantArithmetic_02_6 r
  · exact g32p_row35_variantArithmetic_03_6 r
  · exact g32p_row35_variantArithmetic_04_6 r
  · exact g32p_row35_variantArithmetic_05_6 r
  · exact g32p_row35_variantArithmetic_06_6 r

theorem g32p_row35_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row35_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row35_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 34 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row35_variantArithmetic_00_7 r
  · exact g32p_row35_variantArithmetic_01_7 r
  · exact g32p_row35_variantArithmetic_02_7 r
  · exact g32p_row35_variantArithmetic_03_7 r
  · exact g32p_row35_variantArithmetic_04_7 r
  · exact g32p_row35_variantArithmetic_05_7 r
  · exact g32p_row35_variantArithmetic_06_7 r

theorem g32p_row35_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row35_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row35_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 34 c _ (g32p_row35_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row35_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 34 c _ (g32p_row35_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row35_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 34 c _ (g32p_row35_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row35_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 34 c _ (g32p_row35_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row35_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 34 c _ (g32p_row35_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row35_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 34 c _ (g32p_row35_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row35_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 34 c _ (g32p_row35_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row35_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 34 c _ (g32p_row35_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row35_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup26_source : Fin 384 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 192 then (if i.val < 96 then (if i.val < 48 then (if i.val < 24 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (12, 8) else (80, 16))) else (if i.val < 4 then (85, 71) else (if i.val < 5 then (20, 220) else (30, 49)))) else (if i.val < 9 then (if i.val < 7 then (66, 241) else (if i.val < 8 then (0, 97) else (24, 189))) else (if i.val < 10 then (112, 116) else (if i.val < 11 then (99, 232) else (0, 96))))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then (33, 140) else (if i.val < 14 then (15, 60) else (17, 132))) else (if i.val < 16 then (57, 35) else (if i.val < 17 then (63, 41) else (11, 100)))) else (if i.val < 21 then (if i.val < 19 then (142, 223) else (if i.val < 20 then (85, 14) else (53, 219))) else (if i.val < 22 then (82, 254) else (if i.val < 23 then (116, 194) else (108, 199)))))) else (if i.val < 36 then (if i.val < 30 then (if i.val < 27 then (if i.val < 25 then (30, 107) else (if i.val < 26 then (48, 76) else (62, 33))) else (if i.val < 28 then (13, 94) else (if i.val < 29 then (1, 72) else (5, 217)))) else (if i.val < 33 then (if i.val < 31 then (106, 251) else (if i.val < 32 then (105, 174) else (22, 235))) else (if i.val < 34 then (118, 47) else (if i.val < 35 then (142, 212) else (140, 128))))) else (if i.val < 42 then (if i.val < 39 then (if i.val < 37 then (23, 203) else (if i.val < 38 then (72, 196) else (144, 17))) else (if i.val < 40 then (130, 37) else (if i.val < 41 then (88, 55) else (97, 70)))) else (if i.val < 45 then (if i.val < 43 then (142, 154) else (if i.val < 44 then (141, 78) else (96, 22))) else (if i.val < 46 then (17, 158) else (if i.val < 47 then (143, 162) else (0, 101))))))) else (if i.val < 72 then (if i.val < 60 then (if i.val < 54 then (if i.val < 51 then (if i.val < 49 then (126, 34) else (if i.val < 50 then (142, 43) else (138, 225))) else (if i.val < 52 then (0, 37) else (if i.val < 53 then (120, 16) else (58, 143)))) else (if i.val < 57 then (if i.val < 55 then (101, 35) else (if i.val < 56 then (49, 169) else (134, 128))) else (if i.val < 58 then (125, 33) else (if i.val < 59 then (135, 254) else (73, 26))))) else (if i.val < 66 then (if i.val < 63 then (if i.val < 61 then (97, 212) else (if i.val < 62 then (138, 138) else (70, 181))) else (if i.val < 64 then (20, 23) else (if i.val < 65 then (104, 26) else (84, 130)))) else (if i.val < 69 then (if i.val < 67 then (124, 157) else (if i.val < 68 then (21, 61) else (144, 20))) else (if i.val < 70 then (132, 205) else (if i.val < 71 then (0, 175) else (20, 86)))))) else (if i.val < 84 then (if i.val < 78 then (if i.val < 75 then (if i.val < 73 then (101, 244) else (if i.val < 74 then (62, 166) else (36, 218))) else (if i.val < 76 then (141, 130) else (if i.val < 77 then (43, 217) else (105, 158)))) else (if i.val < 81 then (if i.val < 79 then (52, 28) else (if i.val < 80 then (16, 110) else (131, 245))) else (if i.val < 82 then (75, 154) else (if i.val < 83 then (135, 53) else (82, 147))))) else (if i.val < 90 then (if i.val < 87 then (if i.val < 85 then (142, 39) else (if i.val < 86 then (80, 7) else (15, 190))) else (if i.val < 88 then (22, 151) else (if i.val < 89 then (141, 50) else (23, 133)))) else (if i.val < 93 then (if i.val < 91 then (132, 132) else (if i.val < 92 then (62, 59) else (8, 226))) else (if i.val < 94 then (51, 96) else (if i.val < 95 then (49, 204) else (65, 136)))))))) else (if i.val < 144 then (if i.val < 120 then (if i.val < 108 then (if i.val < 102 then (if i.val < 99 then (if i.val < 97 then (128, 142) else (if i.val < 98 then (100, 250) else (24, 247))) else (if i.val < 100 then (143, 96) else (if i.val < 101 then (43, 201) else (102, 83)))) else (if i.val < 105 then (if i.val < 103 then (135, 187) else (if i.val < 104 then (109, 133) else (70, 109))) else (if i.val < 106 then (99, 149) else (if i.val < 107 then (87, 31) else (79, 168))))) else (if i.val < 114 then (if i.val < 111 then (if i.val < 109 then (23, 69) else (if i.val < 110 then (53, 85) else (129, 150))) else (if i.val < 112 then (42, 142) else (if i.val < 113 then (34, 77) else (45, 166)))) else (if i.val < 117 then (if i.val < 115 then (121, 171) else (if i.val < 116 then (72, 193) else (63, 129))) else (if i.val < 118 then (85, 209) else (if i.val < 119 then (21, 188) else (136, 11)))))) else (if i.val < 132 then (if i.val < 126 then (if i.val < 123 then (if i.val < 121 then (118, 214) else (if i.val < 122 then (21, 55) else (64, 199))) else (if i.val < 124 then (117, 17) else (if i.val < 125 then (129, 148) else (120, 71)))) else (if i.val < 129 then (if i.val < 127 then (115, 143) else (if i.val < 128 then (143, 87) else (57, 210))) else (if i.val < 130 then (115, 162) else (if i.val < 131 then (78, 73) else (52, 125))))) else (if i.val < 138 then (if i.val < 135 then (if i.val < 133 then (144, 203) else (if i.val < 134 then (47, 79) else (143, 207))) else (if i.val < 136 then (141, 241) else (if i.val < 137 then (137, 49) else (48, 42)))) else (if i.val < 141 then (if i.val < 139 then (142, 250) else (if i.val < 140 then (29, 168) else (100, 245))) else (if i.val < 142 then (132, 251) else (if i.val < 143 then (53, 116) else (1, 67))))))) else (if i.val < 168 then (if i.val < 156 then (if i.val < 150 then (if i.val < 147 then (if i.val < 145 then (128, 129) else (if i.val < 146 then (39, 148) else (47, 48))) else (if i.val < 148 then (101, 180) else (if i.val < 149 then (32, 140) else (140, 77)))) else (if i.val < 153 then (if i.val < 151 then (75, 62) else (if i.val < 152 then (106, 140) else (85, 10))) else (if i.val < 154 then (138, 58) else (if i.val < 155 then (35, 78) else (6, 140))))) else (if i.val < 162 then (if i.val < 159 then (if i.val < 157 then (61, 158) else (if i.val < 158 then (126, 133) else (120, 129))) else (if i.val < 160 then (97, 206) else (if i.val < 161 then (34, 236) else (35, 0)))) else (if i.val < 165 then (if i.val < 163 then (34, 111) else (if i.val < 164 then (61, 214) else (142, 129))) else (if i.val < 166 then (105, 144) else (if i.val < 167 then (3, 217) else (81, 212)))))) else (if i.val < 180 then (if i.val < 174 then (if i.val < 171 then (if i.val < 169 then (30, 75) else (if i.val < 170 then (102, 84) else (102, 34))) else (if i.val < 172 then (142, 50) else (if i.val < 173 then (59, 108) else (70, 79)))) else (if i.val < 177 then (if i.val < 175 then (0, 99) else (if i.val < 176 then (140, 163) else (144, 95))) else (if i.val < 178 then (118, 16) else (if i.val < 179 then (126, 121) else (51, 192))))) else (if i.val < 186 then (if i.val < 183 then (if i.val < 181 then (40, 100) else (if i.val < 182 then (143, 91) else (13, 125))) else (if i.val < 184 then (49, 219) else (if i.val < 185 then (63, 198) else (103, 110)))) else (if i.val < 189 then (if i.val < 187 then (67, 148) else (if i.val < 188 then (108, 228) else (130, 13))) else (if i.val < 190 then (29, 171) else (if i.val < 191 then (127, 136) else (125, 120))))))))) else (if i.val < 288 then (if i.val < 240 then (if i.val < 216 then (if i.val < 204 then (if i.val < 198 then (if i.val < 195 then (if i.val < 193 then (38, 167) else (if i.val < 194 then (104, 72) else (133, 168))) else (if i.val < 196 then (16, 108) else (if i.val < 197 then (23, 48) else (22, 48)))) else (if i.val < 201 then (if i.val < 199 then (102, 89) else (if i.val < 200 then (127, 96) else (57, 33))) else (if i.val < 202 then (63, 40) else (if i.val < 203 then (9, 144) else (127, 120))))) else (if i.val < 210 then (if i.val < 207 then (if i.val < 205 then (80, 88) else (if i.val < 206 then (142, 216) else (4, 141))) else (if i.val < 208 then (138, 190) else (if i.val < 209 then (61, 226) else (45, 135)))) else (if i.val < 213 then (if i.val < 211 then (25, 42) else (if i.val < 212 then (18, 199) else (134, 92))) else (if i.val < 214 then (25, 93) else (if i.val < 215 then (47, 221) else (47, 177)))))) else (if i.val < 228 then (if i.val < 222 then (if i.val < 219 then (if i.val < 217 then (47, 131) else (if i.val < 218 then (38, 132) else (106, 63))) else (if i.val < 220 then (22, 16) else (if i.val < 221 then (53, 35) else (140, 65)))) else (if i.val < 225 then (if i.val < 223 then (54, 164) else (if i.val < 224 then (40, 218) else (128, 30))) else (if i.val < 226 then (127, 146) else (if i.val < 227 then (23, 104) else (39, 220))))) else (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then (3, 223) else (if i.val < 230 then (89, 152) else (38, 164))) else (if i.val < 232 then (81, 235) else (if i.val < 233 then (41, 170) else (98, 90)))) else (if i.val < 237 then (if i.val < 235 then (76, 181) else (if i.val < 236 then (115, 63) else (78, 238))) else (if i.val < 238 then (63, 165) else (if i.val < 239 then (38, 20) else (24, 73))))))) else (if i.val < 264 then (if i.val < 252 then (if i.val < 246 then (if i.val < 243 then (if i.val < 241 then (143, 164) else (if i.val < 242 then (95, 36) else (17, 71))) else (if i.val < 244 then (80, 166) else (if i.val < 245 then (86, 146) else (70, 61)))) else (if i.val < 249 then (if i.val < 247 then (137, 92) else (if i.val < 248 then (33, 118) else (33, 32))) else (if i.val < 250 then (68, 200) else (if i.val < 251 then (22, 77) else (71, 16))))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 253 then (99, 212) else (if i.val < 254 then (11, 138) else (69, 224))) else (if i.val < 256 then (64, 56) else (if i.val < 257 then (53, 139) else (30, 121)))) else (if i.val < 261 then (if i.val < 259 then (98, 188) else (if i.val < 260 then (25, 206) else (102, 97))) else (if i.val < 262 then (16, 83) else (if i.val < 263 then (128, 207) else (29, 181)))))) else (if i.val < 276 then (if i.val < 270 then (if i.val < 267 then (if i.val < 265 then (108, 133) else (if i.val < 266 then (15, 249) else (79, 216))) else (if i.val < 268 then (8, 161) else (if i.val < 269 then (98, 150) else (19, 75)))) else (if i.val < 273 then (if i.val < 271 then (138, 179) else (if i.val < 272 then (12, 19) else (35, 67))) else (if i.val < 274 then (137, 232) else (if i.val < 275 then (24, 33) else (20, 199))))) else (if i.val < 282 then (if i.val < 279 then (if i.val < 277 then (106, 151) else (if i.val < 278 then (35, 38) else (132, 167))) else (if i.val < 280 then (100, 54) else (if i.val < 281 then (25, 43) else (78, 172)))) else (if i.val < 285 then (if i.val < 283 then (6, 169) else (if i.val < 284 then (60, 48) else (100, 140))) else (if i.val < 286 then (27, 168) else (if i.val < 287 then (126, 152) else (29, 250)))))))) else (if i.val < 336 then (if i.val < 312 then (if i.val < 300 then (if i.val < 294 then (if i.val < 291 then (if i.val < 289 then (100, 139) else (if i.val < 290 then (3, 81) else (18, 37))) else (if i.val < 292 then (141, 0) else (if i.val < 293 then (113, 64) else (30, 226)))) else (if i.val < 297 then (if i.val < 295 then (120, 191) else (if i.val < 296 then (41, 87) else (71, 30))) else (if i.val < 298 then (102, 91) else (if i.val < 299 then (67, 94) else (141, 240))))) else (if i.val < 306 then (if i.val < 303 then (if i.val < 301 then (42, 252) else (if i.val < 302 then (144, 22) else (61, 200))) else (if i.val < 304 then (53, 89) else (if i.val < 305 then (40, 150) else (39, 221)))) else (if i.val < 309 then (if i.val < 307 then (53, 3) else (if i.val < 308 then (53, 129) else (19, 233))) else (if i.val < 310 then (18, 248) else (if i.val < 311 then (143, 128) else (142, 157)))))) else (if i.val < 324 then (if i.val < 318 then (if i.val < 315 then (if i.val < 313 then (121, 217) else (if i.val < 314 then (105, 51) else (139, 37))) else (if i.val < 316 then (72, 151) else (if i.val < 317 then (99, 174) else (83, 200)))) else (if i.val < 321 then (if i.val < 319 then (63, 139) else (if i.val < 320 then (62, 135) else (73, 189))) else (if i.val < 322 then (143, 203) else (if i.val < 323 then (34, 233) else (24, 110))))) else (if i.val < 330 then (if i.val < 327 then (if i.val < 325 then (124, 134) else (if i.val < 326 then (35, 18) else (73, 140))) else (if i.val < 328 then (57, 211) else (if i.val < 329 then (128, 227) else (142, 108)))) else (if i.val < 333 then (if i.val < 331 then (130, 18) else (if i.val < 332 then (114, 184) else (77, 118))) else (if i.val < 334 then (49, 209) else (if i.val < 335 then (128, 34) else (39, 249))))))) else (if i.val < 360 then (if i.val < 348 then (if i.val < 342 then (if i.val < 339 then (if i.val < 337 then (51, 222) else (if i.val < 338 then (131, 147) else (26, 253))) else (if i.val < 340 then (41, 75) else (if i.val < 341 then (66, 160) else (9, 175)))) else (if i.val < 345 then (if i.val < 343 then (81, 141) else (if i.val < 344 then (38, 17) else (137, 94))) else (if i.val < 346 then (83, 109) else (if i.val < 347 then (136, 222) else (43, 103))))) else (if i.val < 354 then (if i.val < 351 then (if i.val < 349 then (66, 6) else (if i.val < 350 then (58, 65) else (135, 55))) else (if i.val < 352 then (30, 80) else (if i.val < 353 then (112, 126) else (19, 122)))) else (if i.val < 357 then (if i.val < 355 then (19, 21) else (if i.val < 356 then (120, 180) else (105, 146))) else (if i.val < 358 then (20, 160) else (if i.val < 359 then (83, 31) else (52, 77)))))) else (if i.val < 372 then (if i.val < 366 then (if i.val < 363 then (if i.val < 361 then (27, 120) else (if i.val < 362 then (78, 128) else (37, 145))) else (if i.val < 364 then (80, 89) else (if i.val < 365 then (46, 20) else (140, 153)))) else (if i.val < 369 then (if i.val < 367 then (75, 12) else (if i.val < 368 then (129, 49) else (29, 82))) else (if i.val < 370 then (23, 230) else (if i.val < 371 then (22, 101) else (135, 75))))) else (if i.val < 378 then (if i.val < 375 then (if i.val < 373 then (86, 147) else (if i.val < 374 then (131, 111) else (46, 196))) else (if i.val < 376 then (33, 243) else (if i.val < 377 then (46, 227) else (106, 73)))) else (if i.val < 381 then (if i.val < 379 then (19, 56) else (if i.val < 380 then (138, 147) else (34, 151))) else (if i.val < 382 then (35, 80) else (if i.val < 383 then (87, 164) else (99, 183))))))))))

def g32p_supplierGroup26_classify : Fin 384 → Fin 102 :=
  fun i => (if i.val < 192 then (if i.val < 96 then (if i.val < 48 then (if i.val < 24 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 52 else 34)) else (if i.val < 4 then 65 else (if i.val < 5 then 65 else 94))) else (if i.val < 9 then (if i.val < 7 then 38 else (if i.val < 8 then 97 else 49)) else (if i.val < 10 then 38 else (if i.val < 11 then 49 else 96)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then 5 else (if i.val < 14 then 13 else 13)) else (if i.val < 16 then 31 else (if i.val < 17 then 57 else 13))) else (if i.val < 21 then (if i.val < 19 then 57 else (if i.val < 20 then 90 else 69)) else (if i.val < 22 then 18 else (if i.val < 23 then 57 else 18))))) else (if i.val < 36 then (if i.val < 30 then (if i.val < 27 then (if i.val < 25 then 69 else (if i.val < 26 then 13 else 57)) else (if i.val < 28 then 90 else (if i.val < 29 then 69 else 18))) else (if i.val < 33 then (if i.val < 31 then 90 else (if i.val < 32 then 57 else 18)) else (if i.val < 34 then 38 else (if i.val < 35 then 57 else 38)))) else (if i.val < 42 then (if i.val < 39 then (if i.val < 37 then 18 else (if i.val < 38 then 52 else 49)) else (if i.val < 40 then 38 else (if i.val < 41 then 49 else 83))) else (if i.val < 45 then (if i.val < 43 then 57 else (if i.val < 44 then 38 else 69)) else (if i.val < 46 then 13 else (if i.val < 47 then 49 else 101)))))) else (if i.val < 72 then (if i.val < 60 then (if i.val < 54 then (if i.val < 51 then (if i.val < 49 then 57 else (if i.val < 50 then 49 else 57)) else (if i.val < 52 then 37 else (if i.val < 53 then 38 else 49))) else (if i.val < 57 then (if i.val < 55 then 13 else (if i.val < 56 then 34 else 57)) else (if i.val < 58 then 57 else (if i.val < 59 then 38 else 83)))) else (if i.val < 66 then (if i.val < 63 then (if i.val < 61 then 13 else (if i.val < 62 then 49 else 13)) else (if i.val < 64 then 34 else (if i.val < 65 then 57 else 83))) else (if i.val < 69 then (if i.val < 67 then 49 else (if i.val < 68 then 18 else 49)) else (if i.val < 70 then 52 else (if i.val < 71 then 34 else 34))))) else (if i.val < 84 then (if i.val < 78 then (if i.val < 75 then (if i.val < 73 then 49 else (if i.val < 74 then 34 else 34)) else (if i.val < 76 then 49 else (if i.val < 77 then 83 else 34))) else (if i.val < 81 then (if i.val < 79 then 34 else (if i.val < 80 then 5 else 38)) else (if i.val < 82 then 34 else (if i.val < 83 then 38 else 94)))) else (if i.val < 90 then (if i.val < 87 then (if i.val < 85 then 49 else (if i.val < 86 then 34 else 31)) else (if i.val < 88 then 69 else (if i.val < 89 then 38 else 18))) else (if i.val < 93 then (if i.val < 91 then 49 else (if i.val < 92 then 31 else 31)) else (if i.val < 94 then 34 else (if i.val < 95 then 34 else 69))))))) else (if i.val < 144 then (if i.val < 120 then (if i.val < 108 then (if i.val < 102 then (if i.val < 99 then (if i.val < 97 then 38 else (if i.val < 98 then 13 else 82)) else (if i.val < 100 then 38 else (if i.val < 101 then 82 else 13))) else (if i.val < 105 then (if i.val < 103 then 38 else (if i.val < 104 then 94 else 13)) else (if i.val < 106 then 82 else (if i.val < 107 then 49 else 34)))) else (if i.val < 114 then (if i.val < 111 then (if i.val < 109 then 69 else (if i.val < 110 then 94 else 38)) else (if i.val < 112 then 69 else (if i.val < 113 then 13 else 82))) else (if i.val < 117 then (if i.val < 115 then 49 else (if i.val < 116 then 52 else 34)) else (if i.val < 118 then 31 else (if i.val < 119 then 69 else 38))))) else (if i.val < 132 then (if i.val < 126 then (if i.val < 123 then (if i.val < 121 then 38 else (if i.val < 122 then 5 else 69)) else (if i.val < 124 then 38 else (if i.val < 125 then 94 else 38))) else (if i.val < 129 then (if i.val < 127 then 57 else (if i.val < 128 then 38 else 5)) else (if i.val < 130 then 57 else (if i.val < 131 then 34 else 69)))) else (if i.val < 138 then (if i.val < 135 then (if i.val < 133 then 38 else (if i.val < 134 then 82 else 49)) else (if i.val < 136 then 38 else (if i.val < 137 then 49 else 82))) else (if i.val < 141 then (if i.val < 139 then 38 else (if i.val < 140 then 69 else 13)) else (if i.val < 142 then 49 else (if i.val < 143 then 94 else 69)))))) else (if i.val < 168 then (if i.val < 156 then (if i.val < 150 then (if i.val < 147 then (if i.val < 145 then 38 else (if i.val < 146 then 69 else 13)) else (if i.val < 148 then 49 else (if i.val < 149 then 31 else 57))) else (if i.val < 153 then (if i.val < 151 then 49 else (if i.val < 152 then 57 else 90)) else (if i.val < 154 then 49 else (if i.val < 155 then 13 else 34)))) else (if i.val < 162 then (if i.val < 159 then (if i.val < 157 then 57 else (if i.val < 158 then 57 else 38)) else (if i.val < 160 then 13 else (if i.val < 161 then 13 else 49))) else (if i.val < 165 then (if i.val < 163 then 13 else (if i.val < 164 then 34 else 57)) else (if i.val < 166 then 57 else (if i.val < 167 then 34 else 69))))) else (if i.val < 180 then (if i.val < 174 then (if i.val < 171 then (if i.val < 169 then 94 else (if i.val < 170 then 13 else 49)) else (if i.val < 172 then 49 else (if i.val < 173 then 13 else 13))) else (if i.val < 177 then (if i.val < 175 then 99 else (if i.val < 176 then 38 else 57)) else (if i.val < 178 then 38 else (if i.val < 179 then 57 else 34)))) else (if i.val < 186 then (if i.val < 183 then (if i.val < 181 then 69 else (if i.val < 182 then 38 else 90)) else (if i.val < 184 then 34 else (if i.val < 185 then 57 else 34))) else (if i.val < 189 then (if i.val < 187 then 69 else (if i.val < 188 then 38 else 38)) else (if i.val < 190 then 69 else (if i.val < 191 then 90 else 57)))))))) else (if i.val < 288 then (if i.val < 240 then (if i.val < 216 then (if i.val < 204 then (if i.val < 198 then (if i.val < 195 then (if i.val < 193 then 34 else (if i.val < 194 then 34 else 57)) else (if i.val < 196 then 5 else (if i.val < 197 then 69 else 69))) else (if i.val < 201 then (if i.val < 199 then 49 else (if i.val < 200 then 57 else 31)) else (if i.val < 202 then 57 else (if i.val < 203 then 34 else 57)))) else (if i.val < 210 then (if i.val < 207 then (if i.val < 205 then 90 else (if i.val < 206 then 57 else 82)) else (if i.val < 208 then 57 else (if i.val < 209 then 31 else 82))) else (if i.val < 213 then (if i.val < 211 then 52 else (if i.val < 212 then 34 else 57)) else (if i.val < 214 then 83 else (if i.val < 215 then 52 else 82))))) else (if i.val < 228 then (if i.val < 222 then (if i.val < 219 then (if i.val < 217 then 13 else (if i.val < 218 then 34 else 57)) else (if i.val < 220 then 69 else (if i.val < 221 then 69 else 57))) else (if i.val < 225 then (if i.val < 223 then 69 else (if i.val < 224 then 69 else 57)) else (if i.val < 226 then 90 else (if i.val < 227 then 69 else 69)))) else (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 34 else (if i.val < 230 then 57 else 34)) else (if i.val < 232 then 69 else (if i.val < 233 then 69 else 83))) else (if i.val < 237 then (if i.val < 235 then 34 else (if i.val < 236 then 57 else 57)) else (if i.val < 238 then 31 else (if i.val < 239 then 34 else 83)))))) else (if i.val < 264 then (if i.val < 252 then (if i.val < 246 then (if i.val < 243 then (if i.val < 241 then 49 else (if i.val < 242 then 69 else 49)) else (if i.val < 244 then 69 else (if i.val < 245 then 5 else 13))) else (if i.val < 249 then (if i.val < 247 then 49 else (if i.val < 248 then 5 else 5)) else (if i.val < 250 then 69 else (if i.val < 251 then 69 else 13)))) else (if i.val < 258 then (if i.val < 255 then (if i.val < 253 then 49 else (if i.val < 254 then 82 else 83)) else (if i.val < 256 then 5 else (if i.val < 257 then 69 else 94))) else (if i.val < 261 then (if i.val < 259 then 52 else (if i.val < 260 then 83 else 13)) else (if i.val < 262 then 18 else (if i.val < 263 then 94 else 18))))) else (if i.val < 276 then (if i.val < 270 then (if i.val < 267 then (if i.val < 265 then 94 else (if i.val < 266 then 18 else 34)) else (if i.val < 268 then 65 else (if i.val < 269 then 49 else 65))) else (if i.val < 273 then (if i.val < 271 then 49 else (if i.val < 272 then 52 else 13)) else (if i.val < 274 then 49 else (if i.val < 275 then 13 else 34)))) else (if i.val < 282 then (if i.val < 279 then (if i.val < 277 then 65 else (if i.val < 278 then 13 else 49)) else (if i.val < 280 then 83 else (if i.val < 281 then 13 else 34))) else (if i.val < 285 then (if i.val < 283 then 31 else (if i.val < 284 then 13 else 52)) else (if i.val < 286 then 34 else (if i.val < 287 then 57 else 94))))))) else (if i.val < 336 then (if i.val < 312 then (if i.val < 300 then (if i.val < 294 then (if i.val < 291 then (if i.val < 289 then 13 else (if i.val < 290 then 52 else 49)) else (if i.val < 292 then 38 else (if i.val < 293 then 49 else 83))) else (if i.val < 297 then (if i.val < 295 then 38 else (if i.val < 296 then 69 else 13)) else (if i.val < 298 then 49 else (if i.val < 299 then 69 else 38)))) else (if i.val < 306 then (if i.val < 303 then (if i.val < 301 then 69 else (if i.val < 302 then 49 else 31)) else (if i.val < 304 then 69 else (if i.val < 305 then 38 else 38))) else (if i.val < 309 then (if i.val < 307 then 69 else (if i.val < 308 then 69 else 65)) else (if i.val < 310 then 57 else (if i.val < 311 then 49 else 57))))) else (if i.val < 324 then (if i.val < 318 then (if i.val < 315 then (if i.val < 313 then 49 else (if i.val < 314 then 34 else 57)) else (if i.val < 316 then 52 else (if i.val < 317 then 49 else 13))) else (if i.val < 321 then (if i.val < 319 then 34 else (if i.val < 320 then 57 else 52)) else (if i.val < 322 then 49 else (if i.val < 323 then 13 else 83)))) else (if i.val < 330 then (if i.val < 327 then (if i.val < 325 then 49 else (if i.val < 326 then 13 else 49)) else (if i.val < 328 then 5 else (if i.val < 329 then 38 else 57))) else (if i.val < 333 then (if i.val < 331 then 38 else (if i.val < 332 then 57 else 34)) else (if i.val < 334 then 34 else (if i.val < 335 then 57 else 38)))))) else (if i.val < 360 then (if i.val < 348 then (if i.val < 342 then (if i.val < 339 then (if i.val < 337 then 34 else (if i.val < 338 then 57 else 34)) else (if i.val < 340 then 69 else (if i.val < 341 then 69 else 34))) else (if i.val < 345 then (if i.val < 343 then 69 else (if i.val < 344 then 34 else 49)) else (if i.val < 346 then 38 else (if i.val < 347 then 49 else 38)))) else (if i.val < 354 then (if i.val < 351 then (if i.val < 349 then 38 else (if i.val < 350 then 5 else 38)) else (if i.val < 352 then 94 else (if i.val < 353 then 38 else 65))) else (if i.val < 357 then (if i.val < 355 then 65 else (if i.val < 356 then 38 else 90)) else (if i.val < 358 then 65 else (if i.val < 359 then 38 else 90))))) else (if i.val < 372 then (if i.val < 366 then (if i.val < 363 then (if i.val < 361 then 65 else (if i.val < 362 then 90 else 34)) else (if i.val < 364 then 90 else (if i.val < 365 then 13 else 38))) else (if i.val < 369 then (if i.val < 367 then 13 else (if i.val < 368 then 38 else 69)) else (if i.val < 370 then 13 else (if i.val < 371 then 69 else 38)))) else (if i.val < 378 then (if i.val < 375 then (if i.val < 373 then 5 else (if i.val < 374 then 57 else 13)) else (if i.val < 376 then 13 else (if i.val < 377 then 13 else 57))) else (if i.val < 381 then (if i.val < 379 then 31 else (if i.val < 380 then 49 else 13)) else (if i.val < 382 then 13 else (if i.val < 383 then 49 else 13)))))))))

def g32p_supplierGroup26_support : Finset (Fin 102) :=
  {0, 5, 13, 18, 31, 34, 37, 38, 49, 52, 57, 65, 69, 82, 83, 90, 94, 96, 97, 99, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup26_matrix_000 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 0 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 0 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 0 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 0 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 0 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_001 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 1 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 1 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 1 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 1 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 1 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_002 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 2 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 2 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 2 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 2 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 2 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_003 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 3 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 3 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 3 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 3 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 3 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_004 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 4 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 4 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 4 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 4 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 4 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_005 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 5 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 5 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 5 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 5 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 5 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_006 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 6 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 6 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 6 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 6 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 6 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_007 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 7 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 7 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 7 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 7 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 7 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_008 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 8 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 8 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 8 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 8 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 8 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_009 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 9 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 9 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 9 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 9 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 9 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_010 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 10 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 10 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 10 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 10 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 10 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_011 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 11 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 11 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 11 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 11 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 11 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_012 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 12 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 12 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 12 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 12 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 12 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_013 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 13 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 13 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 13 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 13 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 13 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_014 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 14 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 14 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 14 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 14 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 14 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_015 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 15 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 15 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 15 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 15 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 15 r) ∈ g32p_supplierGroup26_support := by
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

theorem g32p_supplierGroup26_matrix_016 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 16 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 16 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 16 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 16 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 16 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_017 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 17 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 17 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 17 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 17 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 17 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_018 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 18 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 18 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 18 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 18 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 18 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_019 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 19 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 19 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 19 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 19 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 19 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_020 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 20 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 20 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 20 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 20 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 20 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_021 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 21 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 21 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 21 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 21 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 21 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_022 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 22 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 22 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 22 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 22 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 22 r) ∈ g32p_supplierGroup26_support := by
  decide +kernel

theorem g32p_supplierGroup26_matrix_023 : ∀ r : Fin 16,
    g32p_row36_groupNodes (g32p_finBlockIndex 384 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 23 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup26_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup26_source (g32p_finBlockIndex 384 23 r)).1 (g32p_supplierGroup26_source (g32p_finBlockIndex 384 23 r)).2 =
      g32p_supplierGroup26_classify (g32p_finBlockIndex 384 23 r) := by
  decide +kernel

theorem g32p_supplierGroup26_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup26_classify (g32p_finBlockIndex 384 23 r) ∈ g32p_supplierGroup26_support := by
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

theorem g32p_supplierGroup26_matrix (i : Fin 384) :
    g32p_row36_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source i).1 (g32p_supplierGroup26_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row36_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup26_source i).1 (g32p_supplierGroup26_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup26_matrix_000 r
  · exact g32p_supplierGroup26_matrix_001 r
  · exact g32p_supplierGroup26_matrix_002 r
  · exact g32p_supplierGroup26_matrix_003 r
  · exact g32p_supplierGroup26_matrix_004 r
  · exact g32p_supplierGroup26_matrix_005 r
  · exact g32p_supplierGroup26_matrix_006 r
  · exact g32p_supplierGroup26_matrix_007 r
  · exact g32p_supplierGroup26_matrix_008 r
  · exact g32p_supplierGroup26_matrix_009 r
  · exact g32p_supplierGroup26_matrix_010 r
  · exact g32p_supplierGroup26_matrix_011 r
  · exact g32p_supplierGroup26_matrix_012 r
  · exact g32p_supplierGroup26_matrix_013 r
  · exact g32p_supplierGroup26_matrix_014 r
  · exact g32p_supplierGroup26_matrix_015 r
  · exact g32p_supplierGroup26_matrix_016 r
  · exact g32p_supplierGroup26_matrix_017 r
  · exact g32p_supplierGroup26_matrix_018 r
  · exact g32p_supplierGroup26_matrix_019 r
  · exact g32p_supplierGroup26_matrix_020 r
  · exact g32p_supplierGroup26_matrix_021 r
  · exact g32p_supplierGroup26_matrix_022 r
  · exact g32p_supplierGroup26_matrix_023 r

theorem g32p_supplierGroup26_class (i : Fin 384) :
    g32p_supplierForest_classes (g32p_supplierGroup26_source i).1 (g32p_supplierGroup26_source i).2 =
      g32p_supplierGroup26_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup26_source i).1 (g32p_supplierGroup26_source i).2 =
      g32p_supplierGroup26_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup26_class_000 r
  · exact g32p_supplierGroup26_class_001 r
  · exact g32p_supplierGroup26_class_002 r
  · exact g32p_supplierGroup26_class_003 r
  · exact g32p_supplierGroup26_class_004 r
  · exact g32p_supplierGroup26_class_005 r
  · exact g32p_supplierGroup26_class_006 r
  · exact g32p_supplierGroup26_class_007 r
  · exact g32p_supplierGroup26_class_008 r
  · exact g32p_supplierGroup26_class_009 r
  · exact g32p_supplierGroup26_class_010 r
  · exact g32p_supplierGroup26_class_011 r
  · exact g32p_supplierGroup26_class_012 r
  · exact g32p_supplierGroup26_class_013 r
  · exact g32p_supplierGroup26_class_014 r
  · exact g32p_supplierGroup26_class_015 r
  · exact g32p_supplierGroup26_class_016 r
  · exact g32p_supplierGroup26_class_017 r
  · exact g32p_supplierGroup26_class_018 r
  · exact g32p_supplierGroup26_class_019 r
  · exact g32p_supplierGroup26_class_020 r
  · exact g32p_supplierGroup26_class_021 r
  · exact g32p_supplierGroup26_class_022 r
  · exact g32p_supplierGroup26_class_023 r

theorem g32p_supplierGroup26_support_mem (i : Fin 384) :
    g32p_supplierGroup26_classify i ∈ g32p_supplierGroup26_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup26_classify i ∈ g32p_supplierGroup26_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup26_support_000 r
  · exact g32p_supplierGroup26_support_001 r
  · exact g32p_supplierGroup26_support_002 r
  · exact g32p_supplierGroup26_support_003 r
  · exact g32p_supplierGroup26_support_004 r
  · exact g32p_supplierGroup26_support_005 r
  · exact g32p_supplierGroup26_support_006 r
  · exact g32p_supplierGroup26_support_007 r
  · exact g32p_supplierGroup26_support_008 r
  · exact g32p_supplierGroup26_support_009 r
  · exact g32p_supplierGroup26_support_010 r
  · exact g32p_supplierGroup26_support_011 r
  · exact g32p_supplierGroup26_support_012 r
  · exact g32p_supplierGroup26_support_013 r
  · exact g32p_supplierGroup26_support_014 r
  · exact g32p_supplierGroup26_support_015 r
  · exact g32p_supplierGroup26_support_016 r
  · exact g32p_supplierGroup26_support_017 r
  · exact g32p_supplierGroup26_support_018 r
  · exact g32p_supplierGroup26_support_019 r
  · exact g32p_supplierGroup26_support_020 r
  · exact g32p_supplierGroup26_support_021 r
  · exact g32p_supplierGroup26_support_022 r
  · exact g32p_supplierGroup26_support_023 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row36_supplierClassifier : Fin 384 → Fin 102 := g32p_supplierGroup26_classify

theorem g32p_row36_groupEquiv_isConj (i : Fin 384) :
    IsConj (g32p_row36_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row36_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup26_source i).1 (g32p_supplierGroup26_source i).2
  rw [g32p_supplierGroup26_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row36_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup26_matrix i)

def g32p_row36_supplierClass (h : (g32p_recordedSuppliers 35).H) : Fin 102 :=
  g32p_row36_supplierClassifier (g32p_row36_groupEquiv.symm h)

theorem g32p_row36_supplierClass_isConj (h : (g32p_recordedSuppliers 35).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row36_supplierClass h)) := by
  have he : (g32p_row36_groupEquiv (g32p_row36_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 35).H => (a : g32p_G))
      (g32p_row36_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row36_supplierClassifier (g32p_row36_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row36_groupEquiv_isConj (g32p_row36_groupEquiv.symm h)

theorem g32p_row36_supplierClass_iff (h : (g32p_recordedSuppliers 35).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row36_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row36_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row36_supplierClass_isConj h).symm

theorem g32p_row36_supplierClass_mem_support (h : (g32p_recordedSuppliers 35).H) :
    g32p_row36_supplierClass h ∈ g32p_supplierGroup26_support :=
  g32p_supplierGroup26_support_mem (g32p_row36_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row36_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 0) (g32p_literalTraceValue 35 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row36_traceCoefficients_000]
  decide +kernel

theorem g32p_row36_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 5 = [4, 0, 0, 8] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 5) (g32p_literalTraceValue 35 5)
      [1, -1, 1] [2304, 2304] = true := by
  rw [g32p_row36_traceCoefficients_005]
  decide +kernel

theorem g32p_row36_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 13 = [0, 0, 20, 0, 0, 24] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 13) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 13) (g32p_literalTraceValue 35 13)
      [1, -1, 1] [0, 0, 6912, 6912] = true := by
  rw [g32p_row36_traceCoefficients_013]
  decide +kernel

theorem g32p_row36_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 18 = [2, 0, 0, 8] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 18) (g32p_literalTraceValue 35 18)
      [1, -1, 1] [13824, 13824] = true := by
  rw [g32p_row36_traceCoefficients_018]
  decide +kernel

theorem g32p_row36_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 31 = [0, 8, 0, 0, 4] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 31) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 31) (g32p_literalTraceValue 35 31)
      [1, -1, 1] [-1152, 1152, 1152] = true := by
  rw [g32p_row36_traceCoefficients_031]
  decide +kernel

theorem g32p_row36_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 34 = [0, 24, 0, 0, 20] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 34) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 34) (g32p_literalTraceValue 35 34)
      [1, -1, 1] [-1152, 5760, 5760] = true := by
  rw [g32p_row36_traceCoefficients_034]
  decide +kernel

theorem g32p_row36_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 37 = [0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 37) (g32p_literalTraceValue 35 37)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row36_traceCoefficients_037]
  decide +kernel

theorem g32p_row36_traceCoefficients_038 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 38 = [32, 0, 0, 16] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_038 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 38) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 38) (g32p_literalTraceValue 35 38)
      [1, -1, 1] [384, 384] = true := by
  rw [g32p_row36_traceCoefficients_038]
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

theorem g32p_row36_traceCoefficients_049 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 49 = [0, 0, 32, 0, 0, 16] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_049 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 49) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 49) (g32p_literalTraceValue 35 49)
      [1, -1, 1] [0, 0, 384, 384] = true := by
  rw [g32p_row36_traceCoefficients_049]
  decide +kernel

theorem g32p_row36_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 52 = [0, 0, 4, 0, 0, 8] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 52) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 52) (g32p_literalTraceValue 35 52)
      [1, -1, 1] [0, 0, 2304, 2304] = true := by
  rw [g32p_row36_traceCoefficients_052]
  decide +kernel

theorem g32p_row36_traceCoefficients_057 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 57 = [0, 16, 0, 0, 32] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_057 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 57) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 57) (g32p_literalTraceValue 35 57)
      [1, -1, 1] [384, 768, 768] = true := by
  rw [g32p_row36_traceCoefficients_057]
  decide +kernel

theorem g32p_row36_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 65 = [0, 8, 0, 0, 2] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 65) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 65) (g32p_literalTraceValue 35 65)
      [1, -1, 1] [-10368, 3456, 3456] = true := by
  rw [g32p_row36_traceCoefficients_065]
  decide +kernel

theorem g32p_row36_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 69 = [20, 0, 0, 24] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 69) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 69) (g32p_literalTraceValue 35 69)
      [1, -1, 1] [6912, 6912] = true := by
  rw [g32p_row36_traceCoefficients_069]
  decide +kernel

theorem g32p_row36_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 82 = [0, 0, 2, 0, 0, 8] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 82) (g32p_literalTraceValue 35 82)
      [1, -1, 1] [0, 0, 13824, 13824] = true := by
  rw [g32p_row36_traceCoefficients_082]
  decide +kernel

theorem g32p_row36_traceCoefficients_083 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 83 = [0, 0, 4, 0, 0, 8] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 83) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 83) (g32p_literalTraceValue 35 83)
      [1, -1, 1] [0, 0, 2304, 2304] = true := by
  rw [g32p_row36_traceCoefficients_083]
  decide +kernel

theorem g32p_row36_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 90 = [0, 8, 0, 0, 4] := by
  decide +kernel

theorem g32p_row36_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 384 (g32p_literalCentralizer 90) 6
      (g32p_supplierTraceCoefficients g32p_row36_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row36_characterValues j)).val) 90) (g32p_literalTraceValue 35 90)
      [1, -1, 1] [-1152, 1152, 1152] = true := by
  rw [g32p_row36_traceCoefficients_090]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
