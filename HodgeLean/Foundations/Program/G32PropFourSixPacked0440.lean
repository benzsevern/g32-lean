import HodgeLean.Foundations.Program.G32PropFourSixPacked0439
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPacked0199
import HodgeLean.Foundations.Program.G32PropFourSixPacked0313
import HodgeLean.Foundations.Program.G32PropFourSixPacked0334
import HodgeLean.Foundations.Program.G32PropFourSixPacked0344
import HodgeLean.Foundations.Program.G32PropFourSixPacked0346
import HodgeLean.Foundations.Program.G32PropFourSixPacked0347
import HodgeLean.Foundations.Program.G32PropFourSixPacked0353
import HodgeLean.Foundations.Program.G32PropFourSixPacked0357
import HodgeLean.Foundations.Program.G32PropFourSixPacked0358
import HodgeLean.Foundations.Program.G32PropFourSixPacked0359
import HodgeLean.Foundations.Program.G32PropFourSixPacked0360
import HodgeLean.Foundations.Program.G32PropFourSixPacked0361
import HodgeLean.Foundations.Program.G32PropFourSixPacked0363
import HodgeLean.Foundations.Program.G32PropFourSixPacked0364
import HodgeLean.Foundations.Program.G32PropFourSixPacked0366
import HodgeLean.Foundations.Program.G32PropFourSixPacked0375
import HodgeLean.Foundations.Program.G32PropFourSixPacked0376
import HodgeLean.Foundations.Program.G32PropFourSixPacked0380
import HodgeLean.Foundations.Program.G32PropFourSixPacked0382
import HodgeLean.Foundations.Program.G32PropFourSixPacked0388
import HodgeLean.Foundations.Program.G32PropFourSixPacked0391
import HodgeLean.Foundations.Program.G32PropFourSixPacked0393
import HodgeLean.Foundations.Program.G32PropFourSixPacked0397
import HodgeLean.Foundations.Program.G32PropFourSixPacked0400
import HodgeLean.Foundations.Program.G32PropFourSixPacked0405
import HodgeLean.Foundations.Program.G32PropFourSixPacked0406
import HodgeLean.Foundations.Program.G32PropFourSixPacked0407
import HodgeLean.Foundations.Program.G32PropFourSixPacked0408
import HodgeLean.Foundations.Program.G32PropFourSixPacked0409
import HodgeLean.Foundations.Program.G32PropFourSixPacked0410
import HodgeLean.Foundations.Program.G32PropFourSixPacked0414
import HodgeLean.Foundations.Program.G32PropFourSixPacked0416
import HodgeLean.Foundations.Program.G32PropFourSixPacked0417
import HodgeLean.Foundations.Program.G32PropFourSixPacked0418
import HodgeLean.Foundations.Program.G32PropFourSixPacked0419
import HodgeLean.Foundations.Program.G32PropFourSixPacked0420
import HodgeLean.Foundations.Program.G32PropFourSixPacked0422
import HodgeLean.Foundations.Program.G32PropFourSixPacked0423
import HodgeLean.Foundations.Program.G32PropFourSixPacked0424
import HodgeLean.Foundations.Program.G32PropFourSixPacked0425
import HodgeLean.Foundations.Program.G32PropFourSixPacked0429
import HodgeLean.Foundations.Program.G32PropFourSixPacked0431
import HodgeLean.Foundations.Program.G32PropFourSixPacked0432
import HodgeLean.Foundations.Program.G32PropFourSixPacked0433
import HodgeLean.Foundations.Program.G32PropFourSixPacked0434
import HodgeLean.Foundations.Program.G32PropFourSixPacked0436
import HodgeLean.Foundations.Program.G32PropFourSixPacked0438
import HodgeLean.Foundations.Program.G32PropFourSixCharacterCoverage
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def g32p_row51_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [3888] else [15552])) else (if i.val < 4 then [1728] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [1296] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [432] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [432] else [432])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else [1296]) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [1296] else [])) else (if i.val < 49 then (if i.val < 48 then [] else [432]) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [432] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [432] else (if i.val < 68 then [15552] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [432])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [3888] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [1728] else (if i.val < 81 then [] else [432]))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [1728] else []) else (if i.val < 88 then [3888] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [432])) else (if i.val < 93 then [] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [15552] else [])))))))

theorem g32p_row51_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup34_support) :
    g32p_supplierTracePolynomialCheck 216 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row51_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row51_characterValues j)).val) c) (g32p_literalTraceValue 50 c)
      [1, 1, 1] (g32p_row51_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row51_tracePolynomial_000
  · exact g32p_row51_tracePolynomial_001
  · exact g32p_row51_tracePolynomial_002
  · exact g32p_row51_tracePolynomial_003
  · exact g32p_row51_tracePolynomial_004
  · exact g32p_row51_tracePolynomial_005
  · exact g32p_row51_tracePolynomial_006
  · exact g32p_row51_tracePolynomial_007
  · exact g32p_row51_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_010
  · exact g32p_row51_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_018
  · exact g32p_row51_tracePolynomial_019
  · exact g32p_row51_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_023
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_040
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_043
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_048
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_050
  · exact g32p_row51_tracePolynomial_051
  · exact g32p_row51_tracePolynomial_052
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_055
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_058
  · exact g32p_row51_tracePolynomial_059
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_061
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_064
  · exact g32p_row51_tracePolynomial_065
  · exact g32p_row51_tracePolynomial_066
  · exact g32p_row51_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_071
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_074
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_076
  · exact g32p_row51_tracePolynomial_077
  · exact g32p_row51_tracePolynomial_078
  · exact g32p_row51_tracePolynomial_079
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_081
  · exact g32p_row51_tracePolynomial_082
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_085
  · exact g32p_row51_tracePolynomial_086
  · exact g32p_row51_tracePolynomial_087
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_089
  · exact g32p_row51_tracePolynomial_090
  · exact g32p_row51_tracePolynomial_091
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_096
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact False.elim ((by decide : (99 : Fin 102) ∉ g32p_supplierGroup34_support) hc)
  · exact g32p_row51_tracePolynomial_100
  · exact g32p_row51_tracePolynomial_101

theorem g32p_row51_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 50 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 50 c) := by
  by_cases hc : c ∈ g32p_supplierGroup34_support
  · have hclass (j : Fin 216) :
        IsConj (g32p_literalRepresentative c) (g32p_row51_groupEquiv j : g32p_G) ↔
          g32p_row51_supplierClassifier j = c := by
      simpa only [g32p_row51_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row51_supplierClass_iff (g32p_row51_groupEquiv j) c
    have hχ (j : Fin 216) :
        (g32p_recordedSupplierCharacters 50 (g32p_row51_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row51_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 50 (show (g32p_recordedSuppliers 50).H from g32p_row51_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row51_characterValues (g32p_row51_groupEquiv.symm (g32p_row51_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 50).H (g32p_recordedSupplierCharacters 50)
      (g32p_literalRepresentative c) g32p_row51_groupEquiv g32p_row51_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row51_characterValues j)).val) c 3 216
      (g32p_literalCentralizer c) (g32p_literalTraceValue 50 c) [1, 1, 1]
      (g32p_row51_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row51_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 50)))
      (g32p_row51_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row51_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row51_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
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

theorem g32p_row51_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
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

theorem g32p_row51_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
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

theorem g32p_row51_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
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

theorem g32p_row51_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
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

theorem g32p_row51_variantArithmetic_05_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_05_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_05_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_05_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_05_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_05_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_05_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_05_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 5 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
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

theorem g32p_row51_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row51_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row51_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
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

theorem g32p_row51_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row51_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row51_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row51_variantArithmetic_00_0 r
  · exact g32p_row51_variantArithmetic_01_0 r
  · exact g32p_row51_variantArithmetic_02_0 r
  · exact g32p_row51_variantArithmetic_03_0 r
  · exact g32p_row51_variantArithmetic_04_0 r
  · exact g32p_row51_variantArithmetic_05_0 r
  · exact g32p_row51_variantArithmetic_06_0 r

theorem g32p_row51_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row51_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row51_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row51_variantArithmetic_00_1 r
  · exact g32p_row51_variantArithmetic_01_1 r
  · exact g32p_row51_variantArithmetic_02_1 r
  · exact g32p_row51_variantArithmetic_03_1 r
  · exact g32p_row51_variantArithmetic_04_1 r
  · exact g32p_row51_variantArithmetic_05_1 r
  · exact g32p_row51_variantArithmetic_06_1 r

theorem g32p_row51_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row51_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row51_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row51_variantArithmetic_00_2 r
  · exact g32p_row51_variantArithmetic_01_2 r
  · exact g32p_row51_variantArithmetic_02_2 r
  · exact g32p_row51_variantArithmetic_03_2 r
  · exact g32p_row51_variantArithmetic_04_2 r
  · exact g32p_row51_variantArithmetic_05_2 r
  · exact g32p_row51_variantArithmetic_06_2 r

theorem g32p_row51_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row51_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row51_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row51_variantArithmetic_00_3 r
  · exact g32p_row51_variantArithmetic_01_3 r
  · exact g32p_row51_variantArithmetic_02_3 r
  · exact g32p_row51_variantArithmetic_03_3 r
  · exact g32p_row51_variantArithmetic_04_3 r
  · exact g32p_row51_variantArithmetic_05_3 r
  · exact g32p_row51_variantArithmetic_06_3 r

theorem g32p_row51_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row51_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row51_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row51_variantArithmetic_00_4 r
  · exact g32p_row51_variantArithmetic_01_4 r
  · exact g32p_row51_variantArithmetic_02_4 r
  · exact g32p_row51_variantArithmetic_03_4 r
  · exact g32p_row51_variantArithmetic_04_4 r
  · exact g32p_row51_variantArithmetic_05_4 r
  · exact g32p_row51_variantArithmetic_06_4 r

theorem g32p_row51_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row51_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row51_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row51_variantArithmetic_00_5 r
  · exact g32p_row51_variantArithmetic_01_5 r
  · exact g32p_row51_variantArithmetic_02_5 r
  · exact g32p_row51_variantArithmetic_03_5 r
  · exact g32p_row51_variantArithmetic_04_5 r
  · exact g32p_row51_variantArithmetic_05_5 r
  · exact g32p_row51_variantArithmetic_06_5 r

theorem g32p_row51_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row51_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row51_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row51_variantArithmetic_00_6 r
  · exact g32p_row51_variantArithmetic_01_6 r
  · exact g32p_row51_variantArithmetic_02_6 r
  · exact g32p_row51_variantArithmetic_03_6 r
  · exact g32p_row51_variantArithmetic_04_6 r
  · exact g32p_row51_variantArithmetic_05_6 r
  · exact g32p_row51_variantArithmetic_06_6 r

theorem g32p_row51_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row51_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row51_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 50 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row51_variantArithmetic_00_7 r
  · exact g32p_row51_variantArithmetic_01_7 r
  · exact g32p_row51_variantArithmetic_02_7 r
  · exact g32p_row51_variantArithmetic_03_7 r
  · exact g32p_row51_variantArithmetic_04_7 r
  · exact g32p_row51_variantArithmetic_05_7 r
  · exact g32p_row51_variantArithmetic_06_7 r

theorem g32p_row51_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row51_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row51_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 50 c _ (g32p_row51_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row51_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 50 c _ (g32p_row51_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row51_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 50 c _ (g32p_row51_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row51_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 50 c _ (g32p_row51_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row51_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 50 c _ (g32p_row51_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row51_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 50 c _ (g32p_row51_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row51_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 50 c _ (g32p_row51_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row51_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 50 c _ (g32p_row51_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row51_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def g32p_allSupplierGeneratorIndex : Fin 51 → Fin 8 → Fin 408 :=
  fun i => (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then g32p_determinantTraceRowIndex else (if i.val < 2 then g32p_row02_generatorIndex else g32p_row03_generatorIndex)) else (if i.val < 4 then g32p_row04_generatorIndex else (if i.val < 5 then g32p_row05_generatorIndex else g32p_row06_generatorIndex))) else (if i.val < 9 then (if i.val < 7 then g32p_row07_generatorIndex else (if i.val < 8 then g32p_row08_generatorIndex else g32p_row09_generatorIndex)) else (if i.val < 10 then g32p_row10_generatorIndex else (if i.val < 11 then g32p_row11_generatorIndex else g32p_row12_generatorIndex)))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then g32p_row13_generatorIndex else (if i.val < 14 then g32p_row14_generatorIndex else g32p_row15_generatorIndex)) else (if i.val < 16 then g32p_row16_generatorIndex else (if i.val < 17 then g32p_row17_generatorIndex else g32p_row18_generatorIndex))) else (if i.val < 21 then (if i.val < 19 then g32p_row19_generatorIndex else (if i.val < 20 then g32p_row20_generatorIndex else g32p_row21_generatorIndex)) else (if i.val < 23 then (if i.val < 22 then g32p_row22_generatorIndex else g32p_row23_generatorIndex) else (if i.val < 24 then g32p_row24_generatorIndex else g32p_row25_generatorIndex))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then g32p_row26_generatorIndex else (if i.val < 27 then g32p_row27_generatorIndex else g32p_row28_generatorIndex)) else (if i.val < 29 then g32p_row29_generatorIndex else (if i.val < 30 then g32p_row30_generatorIndex else g32p_row31_generatorIndex))) else (if i.val < 34 then (if i.val < 32 then g32p_row32_generatorIndex else (if i.val < 33 then g32p_row33_generatorIndex else g32p_row34_generatorIndex)) else (if i.val < 36 then (if i.val < 35 then g32p_row35_generatorIndex else g32p_row36_generatorIndex) else (if i.val < 37 then g32p_row37_generatorIndex else g32p_row38_generatorIndex)))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then g32p_row39_generatorIndex else (if i.val < 40 then g32p_row40_generatorIndex else g32p_row41_generatorIndex)) else (if i.val < 42 then g32p_row42_generatorIndex else (if i.val < 43 then g32p_row43_generatorIndex else g32p_row44_generatorIndex))) else (if i.val < 47 then (if i.val < 45 then g32p_row45_generatorIndex else (if i.val < 46 then g32p_row46_generatorIndex else g32p_row47_generatorIndex)) else (if i.val < 49 then (if i.val < 48 then g32p_row48_generatorIndex else g32p_row49_generatorIndex) else (if i.val < 50 then g32p_row50_generatorIndex else g32p_row51_generatorIndex))))))

def g32p_allSupplierGeneratorDecode : Fin 408 → Fin 51 × Fin 8 :=
  fun i => (if i.val < 204 then (if i.val < 102 then (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (1, 0) else (2, 0))) else (if i.val < 4 then (3, 0) else (if i.val < 5 then (4, 0) else (5, 0)))) else (if i.val < 9 then (if i.val < 7 then (6, 0) else (if i.val < 8 then (7, 0) else (8, 0))) else (if i.val < 10 then (9, 0) else (if i.val < 11 then (10, 0) else (11, 0))))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then (12, 0) else (if i.val < 14 then (13, 0) else (14, 0))) else (if i.val < 16 then (15, 0) else (if i.val < 17 then (16, 0) else (17, 0)))) else (if i.val < 21 then (if i.val < 19 then (18, 0) else (if i.val < 20 then (19, 0) else (20, 0))) else (if i.val < 23 then (if i.val < 22 then (21, 0) else (22, 0)) else (if i.val < 24 then (23, 0) else (24, 0)))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then (25, 0) else (if i.val < 27 then (26, 0) else (27, 0))) else (if i.val < 29 then (28, 0) else (if i.val < 30 then (29, 0) else (30, 0)))) else (if i.val < 34 then (if i.val < 32 then (31, 0) else (if i.val < 33 then (32, 0) else (33, 0))) else (if i.val < 36 then (if i.val < 35 then (34, 0) else (35, 0)) else (if i.val < 37 then (36, 0) else (37, 0))))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then (38, 0) else (if i.val < 40 then (39, 0) else (40, 0))) else (if i.val < 42 then (41, 0) else (if i.val < 43 then (42, 0) else (43, 0)))) else (if i.val < 47 then (if i.val < 45 then (44, 0) else (if i.val < 46 then (45, 0) else (46, 0))) else (if i.val < 49 then (if i.val < 48 then (47, 0) else (48, 0)) else (if i.val < 50 then (49, 0) else (50, 0))))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then (0, 1) else (if i.val < 53 then (1, 1) else (2, 1))) else (if i.val < 55 then (3, 1) else (if i.val < 56 then (4, 1) else (5, 1)))) else (if i.val < 60 then (if i.val < 58 then (6, 1) else (if i.val < 59 then (7, 1) else (8, 1))) else (if i.val < 61 then (9, 1) else (if i.val < 62 then (10, 1) else (11, 1))))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then (12, 1) else (if i.val < 65 then (13, 1) else (14, 1))) else (if i.val < 67 then (15, 1) else (if i.val < 68 then (16, 1) else (17, 1)))) else (if i.val < 72 then (if i.val < 70 then (18, 1) else (if i.val < 71 then (19, 1) else (20, 1))) else (if i.val < 74 then (if i.val < 73 then (21, 1) else (22, 1)) else (if i.val < 75 then (23, 1) else (24, 1)))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then (25, 1) else (if i.val < 78 then (26, 1) else (27, 1))) else (if i.val < 80 then (28, 1) else (if i.val < 81 then (29, 1) else (30, 1)))) else (if i.val < 85 then (if i.val < 83 then (31, 1) else (if i.val < 84 then (32, 1) else (33, 1))) else (if i.val < 87 then (if i.val < 86 then (34, 1) else (35, 1)) else (if i.val < 88 then (36, 1) else (37, 1))))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then (38, 1) else (if i.val < 91 then (39, 1) else (40, 1))) else (if i.val < 93 then (41, 1) else (if i.val < 94 then (42, 1) else (43, 1)))) else (if i.val < 98 then (if i.val < 96 then (44, 1) else (if i.val < 97 then (45, 1) else (46, 1))) else (if i.val < 100 then (if i.val < 99 then (47, 1) else (48, 1)) else (if i.val < 101 then (49, 1) else (50, 1)))))))) else (if i.val < 153 then (if i.val < 127 then (if i.val < 114 then (if i.val < 108 then (if i.val < 105 then (if i.val < 103 then (0, 2) else (if i.val < 104 then (1, 2) else (2, 2))) else (if i.val < 106 then (3, 2) else (if i.val < 107 then (4, 2) else (5, 2)))) else (if i.val < 111 then (if i.val < 109 then (6, 2) else (if i.val < 110 then (7, 2) else (8, 2))) else (if i.val < 112 then (9, 2) else (if i.val < 113 then (10, 2) else (11, 2))))) else (if i.val < 120 then (if i.val < 117 then (if i.val < 115 then (12, 2) else (if i.val < 116 then (13, 2) else (14, 2))) else (if i.val < 118 then (15, 2) else (if i.val < 119 then (16, 2) else (17, 2)))) else (if i.val < 123 then (if i.val < 121 then (18, 2) else (if i.val < 122 then (19, 2) else (20, 2))) else (if i.val < 125 then (if i.val < 124 then (21, 2) else (22, 2)) else (if i.val < 126 then (23, 2) else (24, 2)))))) else (if i.val < 140 then (if i.val < 133 then (if i.val < 130 then (if i.val < 128 then (25, 2) else (if i.val < 129 then (26, 2) else (27, 2))) else (if i.val < 131 then (28, 2) else (if i.val < 132 then (29, 2) else (30, 2)))) else (if i.val < 136 then (if i.val < 134 then (31, 2) else (if i.val < 135 then (32, 2) else (33, 2))) else (if i.val < 138 then (if i.val < 137 then (34, 2) else (35, 2)) else (if i.val < 139 then (36, 2) else (37, 2))))) else (if i.val < 146 then (if i.val < 143 then (if i.val < 141 then (38, 2) else (if i.val < 142 then (39, 2) else (40, 2))) else (if i.val < 144 then (41, 2) else (if i.val < 145 then (42, 2) else (43, 2)))) else (if i.val < 149 then (if i.val < 147 then (44, 2) else (if i.val < 148 then (45, 2) else (46, 2))) else (if i.val < 151 then (if i.val < 150 then (47, 2) else (48, 2)) else (if i.val < 152 then (49, 2) else (50, 2))))))) else (if i.val < 178 then (if i.val < 165 then (if i.val < 159 then (if i.val < 156 then (if i.val < 154 then (0, 3) else (if i.val < 155 then (1, 3) else (2, 3))) else (if i.val < 157 then (3, 3) else (if i.val < 158 then (4, 3) else (5, 3)))) else (if i.val < 162 then (if i.val < 160 then (6, 3) else (if i.val < 161 then (7, 3) else (8, 3))) else (if i.val < 163 then (9, 3) else (if i.val < 164 then (10, 3) else (11, 3))))) else (if i.val < 171 then (if i.val < 168 then (if i.val < 166 then (12, 3) else (if i.val < 167 then (13, 3) else (14, 3))) else (if i.val < 169 then (15, 3) else (if i.val < 170 then (16, 3) else (17, 3)))) else (if i.val < 174 then (if i.val < 172 then (18, 3) else (if i.val < 173 then (19, 3) else (20, 3))) else (if i.val < 176 then (if i.val < 175 then (21, 3) else (22, 3)) else (if i.val < 177 then (23, 3) else (24, 3)))))) else (if i.val < 191 then (if i.val < 184 then (if i.val < 181 then (if i.val < 179 then (25, 3) else (if i.val < 180 then (26, 3) else (27, 3))) else (if i.val < 182 then (28, 3) else (if i.val < 183 then (29, 3) else (30, 3)))) else (if i.val < 187 then (if i.val < 185 then (31, 3) else (if i.val < 186 then (32, 3) else (33, 3))) else (if i.val < 189 then (if i.val < 188 then (34, 3) else (35, 3)) else (if i.val < 190 then (36, 3) else (37, 3))))) else (if i.val < 197 then (if i.val < 194 then (if i.val < 192 then (38, 3) else (if i.val < 193 then (39, 3) else (40, 3))) else (if i.val < 195 then (41, 3) else (if i.val < 196 then (42, 3) else (43, 3)))) else (if i.val < 200 then (if i.val < 198 then (44, 3) else (if i.val < 199 then (45, 3) else (46, 3))) else (if i.val < 202 then (if i.val < 201 then (47, 3) else (48, 3)) else (if i.val < 203 then (49, 3) else (50, 3))))))))) else (if i.val < 306 then (if i.val < 255 then (if i.val < 229 then (if i.val < 216 then (if i.val < 210 then (if i.val < 207 then (if i.val < 205 then (0, 4) else (if i.val < 206 then (0, 5) else (1, 4))) else (if i.val < 208 then (1, 5) else (if i.val < 209 then (2, 4) else (2, 5)))) else (if i.val < 213 then (if i.val < 211 then (3, 4) else (if i.val < 212 then (3, 5) else (4, 4))) else (if i.val < 214 then (4, 5) else (if i.val < 215 then (5, 4) else (5, 5))))) else (if i.val < 222 then (if i.val < 219 then (if i.val < 217 then (6, 4) else (if i.val < 218 then (6, 5) else (7, 4))) else (if i.val < 220 then (7, 5) else (if i.val < 221 then (8, 4) else (8, 5)))) else (if i.val < 225 then (if i.val < 223 then (9, 4) else (if i.val < 224 then (9, 5) else (10, 4))) else (if i.val < 227 then (if i.val < 226 then (10, 5) else (11, 4)) else (if i.val < 228 then (11, 5) else (12, 4)))))) else (if i.val < 242 then (if i.val < 235 then (if i.val < 232 then (if i.val < 230 then (12, 5) else (if i.val < 231 then (13, 4) else (13, 5))) else (if i.val < 233 then (14, 4) else (if i.val < 234 then (14, 5) else (15, 4)))) else (if i.val < 238 then (if i.val < 236 then (15, 5) else (if i.val < 237 then (16, 4) else (16, 5))) else (if i.val < 240 then (if i.val < 239 then (17, 4) else (17, 5)) else (if i.val < 241 then (18, 4) else (18, 5))))) else (if i.val < 248 then (if i.val < 245 then (if i.val < 243 then (19, 4) else (if i.val < 244 then (19, 5) else (20, 4))) else (if i.val < 246 then (20, 5) else (if i.val < 247 then (21, 4) else (21, 5)))) else (if i.val < 251 then (if i.val < 249 then (22, 4) else (if i.val < 250 then (22, 5) else (23, 4))) else (if i.val < 253 then (if i.val < 252 then (23, 5) else (24, 4)) else (if i.val < 254 then (24, 5) else (25, 4))))))) else (if i.val < 280 then (if i.val < 267 then (if i.val < 261 then (if i.val < 258 then (if i.val < 256 then (25, 5) else (if i.val < 257 then (26, 4) else (26, 5))) else (if i.val < 259 then (27, 4) else (if i.val < 260 then (27, 5) else (28, 4)))) else (if i.val < 264 then (if i.val < 262 then (28, 5) else (if i.val < 263 then (29, 4) else (29, 5))) else (if i.val < 265 then (30, 4) else (if i.val < 266 then (30, 5) else (31, 4))))) else (if i.val < 273 then (if i.val < 270 then (if i.val < 268 then (31, 5) else (if i.val < 269 then (32, 4) else (32, 5))) else (if i.val < 271 then (33, 4) else (if i.val < 272 then (33, 5) else (34, 4)))) else (if i.val < 276 then (if i.val < 274 then (34, 5) else (if i.val < 275 then (35, 4) else (35, 5))) else (if i.val < 278 then (if i.val < 277 then (36, 4) else (36, 5)) else (if i.val < 279 then (37, 4) else (37, 5)))))) else (if i.val < 293 then (if i.val < 286 then (if i.val < 283 then (if i.val < 281 then (38, 4) else (if i.val < 282 then (38, 5) else (39, 4))) else (if i.val < 284 then (39, 5) else (if i.val < 285 then (40, 4) else (40, 5)))) else (if i.val < 289 then (if i.val < 287 then (41, 4) else (if i.val < 288 then (41, 5) else (42, 4))) else (if i.val < 291 then (if i.val < 290 then (42, 5) else (43, 4)) else (if i.val < 292 then (43, 5) else (44, 4))))) else (if i.val < 299 then (if i.val < 296 then (if i.val < 294 then (44, 5) else (if i.val < 295 then (45, 4) else (45, 5))) else (if i.val < 297 then (46, 4) else (if i.val < 298 then (46, 5) else (47, 4)))) else (if i.val < 302 then (if i.val < 300 then (47, 5) else (if i.val < 301 then (48, 4) else (48, 5))) else (if i.val < 304 then (if i.val < 303 then (49, 4) else (49, 5)) else (if i.val < 305 then (50, 4) else (50, 5)))))))) else (if i.val < 357 then (if i.val < 331 then (if i.val < 318 then (if i.val < 312 then (if i.val < 309 then (if i.val < 307 then (0, 6) else (if i.val < 308 then (0, 7) else (1, 6))) else (if i.val < 310 then (1, 7) else (if i.val < 311 then (2, 6) else (2, 7)))) else (if i.val < 315 then (if i.val < 313 then (3, 6) else (if i.val < 314 then (3, 7) else (4, 6))) else (if i.val < 316 then (4, 7) else (if i.val < 317 then (5, 6) else (5, 7))))) else (if i.val < 324 then (if i.val < 321 then (if i.val < 319 then (6, 6) else (if i.val < 320 then (6, 7) else (7, 6))) else (if i.val < 322 then (7, 7) else (if i.val < 323 then (8, 6) else (8, 7)))) else (if i.val < 327 then (if i.val < 325 then (9, 6) else (if i.val < 326 then (9, 7) else (10, 6))) else (if i.val < 329 then (if i.val < 328 then (10, 7) else (11, 6)) else (if i.val < 330 then (11, 7) else (12, 6)))))) else (if i.val < 344 then (if i.val < 337 then (if i.val < 334 then (if i.val < 332 then (12, 7) else (if i.val < 333 then (13, 6) else (13, 7))) else (if i.val < 335 then (14, 6) else (if i.val < 336 then (14, 7) else (15, 6)))) else (if i.val < 340 then (if i.val < 338 then (15, 7) else (if i.val < 339 then (16, 6) else (16, 7))) else (if i.val < 342 then (if i.val < 341 then (17, 6) else (17, 7)) else (if i.val < 343 then (18, 6) else (18, 7))))) else (if i.val < 350 then (if i.val < 347 then (if i.val < 345 then (19, 6) else (if i.val < 346 then (19, 7) else (20, 6))) else (if i.val < 348 then (20, 7) else (if i.val < 349 then (21, 6) else (21, 7)))) else (if i.val < 353 then (if i.val < 351 then (22, 6) else (if i.val < 352 then (22, 7) else (23, 6))) else (if i.val < 355 then (if i.val < 354 then (23, 7) else (24, 6)) else (if i.val < 356 then (24, 7) else (25, 6))))))) else (if i.val < 382 then (if i.val < 369 then (if i.val < 363 then (if i.val < 360 then (if i.val < 358 then (25, 7) else (if i.val < 359 then (26, 6) else (26, 7))) else (if i.val < 361 then (27, 6) else (if i.val < 362 then (27, 7) else (28, 6)))) else (if i.val < 366 then (if i.val < 364 then (28, 7) else (if i.val < 365 then (29, 6) else (29, 7))) else (if i.val < 367 then (30, 6) else (if i.val < 368 then (30, 7) else (31, 6))))) else (if i.val < 375 then (if i.val < 372 then (if i.val < 370 then (31, 7) else (if i.val < 371 then (32, 6) else (32, 7))) else (if i.val < 373 then (33, 6) else (if i.val < 374 then (33, 7) else (34, 6)))) else (if i.val < 378 then (if i.val < 376 then (34, 7) else (if i.val < 377 then (35, 6) else (35, 7))) else (if i.val < 380 then (if i.val < 379 then (36, 6) else (36, 7)) else (if i.val < 381 then (37, 6) else (37, 7)))))) else (if i.val < 395 then (if i.val < 388 then (if i.val < 385 then (if i.val < 383 then (38, 6) else (if i.val < 384 then (38, 7) else (39, 6))) else (if i.val < 386 then (39, 7) else (if i.val < 387 then (40, 6) else (40, 7)))) else (if i.val < 391 then (if i.val < 389 then (41, 6) else (if i.val < 390 then (41, 7) else (42, 6))) else (if i.val < 393 then (if i.val < 392 then (42, 7) else (43, 6)) else (if i.val < 394 then (43, 7) else (44, 6))))) else (if i.val < 401 then (if i.val < 398 then (if i.val < 396 then (44, 7) else (if i.val < 397 then (45, 6) else (45, 7))) else (if i.val < 399 then (46, 6) else (if i.val < 400 then (46, 7) else (47, 6)))) else (if i.val < 404 then (if i.val < 402 then (47, 7) else (if i.val < 403 then (48, 6) else (48, 7))) else (if i.val < 406 then (if i.val < 405 then (49, 6) else (49, 7)) else (if i.val < 407 then (50, 6) else (50, 7))))))))))

theorem g32p_allSupplierGeneratorDecode_index : ∀ j : Fin 408,
    g32p_allSupplierGeneratorIndex (g32p_allSupplierGeneratorDecode j).1
      (g32p_allSupplierGeneratorDecode j).2 = j := by
  decide +kernel

theorem g32p_allSupplierTrace_actual (i : Fin 51) (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_allSupplierGeneratorIndex i k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega
        (g32p_literalTraceValue (g32p_allSupplierGeneratorIndex i k) c) := by
  fin_cases i
  · exact g32p_determinantSupplier_literalTrace_actual c k
  · exact g32p_row02_all_literalTrace_actual c k
  · exact g32p_row03_all_literalTrace_actual c k
  · exact g32p_row04_all_literalTrace_actual c k
  · exact g32p_row05_all_literalTrace_actual c k
  · exact g32p_row06_all_literalTrace_actual c k
  · exact g32p_row07_all_literalTrace_actual c k
  · exact g32p_row08_all_literalTrace_actual c k
  · exact g32p_row09_all_literalTrace_actual c k
  · exact g32p_row10_all_literalTrace_actual c k
  · exact g32p_row11_all_literalTrace_actual c k
  · exact g32p_row12_all_literalTrace_actual c k
  · exact g32p_row13_all_literalTrace_actual c k
  · exact g32p_row14_all_literalTrace_actual c k
  · exact g32p_row15_all_literalTrace_actual c k
  · exact g32p_row16_all_literalTrace_actual c k
  · exact g32p_row17_all_literalTrace_actual c k
  · exact g32p_row18_all_literalTrace_actual c k
  · exact g32p_row19_all_literalTrace_actual c k
  · exact g32p_row20_all_literalTrace_actual c k
  · exact g32p_row21_all_literalTrace_actual c k
  · exact g32p_row22_all_literalTrace_actual c k
  · exact g32p_row23_all_literalTrace_actual c k
  · exact g32p_row24_all_literalTrace_actual c k
  · exact g32p_row25_all_literalTrace_actual c k
  · exact g32p_row26_all_literalTrace_actual c k
  · exact g32p_row27_all_literalTrace_actual c k
  · exact g32p_row28_all_literalTrace_actual c k
  · exact g32p_row29_all_literalTrace_actual c k
  · exact g32p_row30_all_literalTrace_actual c k
  · exact g32p_row31_all_literalTrace_actual c k
  · exact g32p_row32_all_literalTrace_actual c k
  · exact g32p_row33_all_literalTrace_actual c k
  · exact g32p_row34_all_literalTrace_actual c k
  · exact g32p_row35_all_literalTrace_actual c k
  · exact g32p_row36_all_literalTrace_actual c k
  · exact g32p_row37_all_literalTrace_actual c k
  · exact g32p_row38_all_literalTrace_actual c k
  · exact g32p_row39_all_literalTrace_actual c k
  · exact g32p_row40_all_literalTrace_actual c k
  · exact g32p_row41_all_literalTrace_actual c k
  · exact g32p_row42_all_literalTrace_actual c k
  · exact g32p_row43_all_literalTrace_actual c k
  · exact g32p_row44_all_literalTrace_actual c k
  · exact g32p_row45_all_literalTrace_actual c k
  · exact g32p_row46_all_literalTrace_actual c k
  · exact g32p_row47_all_literalTrace_actual c k
  · exact g32p_row48_all_literalTrace_actual c k
  · exact g32p_row49_all_literalTrace_actual c k
  · exact g32p_row50_all_literalTrace_actual c k
  · exact g32p_row51_all_literalTrace_actual c k

theorem g32p_recordedInductionGenerators_literalTrace_actual (j : Fin 408) (c : Fin 102) :
    (g32p_recordedInductionGenerators j).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue j c) := by
  rw [← g32p_allSupplierGeneratorDecode_index j]
  exact g32p_allSupplierTrace_actual _ c _

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory
open scoped Classical

set_option maxHeartbeats 400000

theorem g32p_integer_norm_one {I : Type*} [Fintype I] (c : I → ℤ)
    (hc : ∑ i, c i ^ 2 = 1) :
    ∃ i, (c i = 1 ∨ c i = -1) ∧ ∀ j, j ≠ i → c j = 0 := by
  classical
  have hex : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    simp only [h, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at hc
    norm_num at hc
  obtain ⟨i, hi⟩ := hex
  have hle (j : I) : c j ^ 2 ≤ 1 := by
    rw [← hc]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (c k)) (Finset.mem_univ j)
  have hunit : c i = 1 ∨ c i = -1 := by
    have := hle i
    have : c i ≤ -1 ∨ 1 ≤ c i := by omega
    rcases this with h | h <;> [right; left] <;> nlinarith
  refine ⟨i, hunit, fun j hji => ?_⟩
  have hij : c i ^ 2 + c j ^ 2 ≤ 1 := by
    rw [← hc]
    have hh := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({i, j} : Finset I) ⊆ Finset.univ from Finset.subset_univ _)
      (fun k _ _ => sq_nonneg (c k))
    simpa only [Finset.sum_pair (Ne.symm hji)] using hh
  rcases hunit with h | h <;> rw [h] at hij <;> nlinarith [sq_nonneg (c j)]

theorem g32p_virtual_simple_expansion_norm {G I : Type*} [Group G] [Fintype G]
    [Fintype I] (V : I → FDRep ℂ G) (hS : ∀ i, Simple (V i))
    (hN : ∀ i j, i ≠ j → IsEmpty (V i ≅ V j)) (c : I → ℤ) :
    (Nat.card G : ℂ)⁻¹ * ∑ g,
      (∑ i, (c i : ℂ) * (V i).character g) *
      (∑ i, (c i : ℂ) * (V i).character g⁻¹) = ∑ i, (c i : ℂ) ^ 2 := by
  classical
  let : ∀ i, Simple (V i) := hS
  have hp (i j : I) : g32p_characterPairing (V j) (V i).character =
      if i = j then 1 else 0 := by
    rw [g32p_characterPairing_simple]
    split_ifs with h hi
    · rfl
    · exact False.elim ((hN i j hi).false h.some)
    · subst j
      exact False.elim (h ⟨Iso.refl _⟩)
    · rfl
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ (α := G))]
  have ht (i j : I) :
      ∑ g, (Nat.card G : ℂ)⁻¹ *
        ((c i : ℂ) * (V i).character g * ((c j : ℂ) * (V j).character g⁻¹)) =
      (c i : ℂ) * (c j : ℂ) * (if i = j then 1 else 0) := by
    rw [← Finset.mul_sum, ← hp]
    unfold g32p_characterPairing
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [show ∀ g, (c i : ℂ) * (V i).character g *
        ((c j : ℂ) * (V j).character g⁻¹) =
        ((c i : ℂ) * (c j : ℂ)) * ((V i).character g * (V j).character g⁻¹) by
      intro g; ring, ← Finset.mul_sum]
    ring
  simp_rw [ht, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, pow_two]

theorem g32p_realize_simple_integer_expansion {G I : Type*} [Group G] [Fintype G]
    [Fintype I] (V : I → FDRep ℂ G) (hS : ∀ i, Simple (V i))
    (hN : ∀ i j, i ≠ j → IsEmpty (V i ≅ V j)) (c : I → ℤ) (f : G → ℂ)
    (hf : ∀ g, f g = ∑ i, (c i : ℂ) * (V i).character g)
    (hnorm : (Nat.card G : ℂ)⁻¹ * ∑ g, f g * f g⁻¹ = 1)
    (hpos : 0 < (f 1).re) :
    ∃ W : FDRep ℂ G, Simple W ∧ W.character = f := by
  classical
  have hs : ∑ i, c i ^ 2 = 1 := by
    have hh := g32p_virtual_simple_expansion_norm V hS hN c
    simp_rw [← hf] at hh
    rw [hnorm] at hh
    exact_mod_cast hh.symm
  obtain ⟨i, hi, hz⟩ := g32p_integer_norm_one c hs
  have heq (g : G) : f g = (c i : ℂ) * (V i).character g := by
    rw [hf]
    exact Finset.sum_eq_single i (fun j _ hji => by rw [hz j hji]; simp)
      (fun h => False.elim (h (Finset.mem_univ i)))
  have hc : c i = 1 := by
    rcases hi with hi | hi
    · exact hi
    · have hh := heq 1
      rw [hi, FDRep.char_one] at hh
      have hr := congrArg Complex.re hh
      simp only [Int.cast_neg, Int.cast_one, neg_one_mul, Complex.neg_re,
        Complex.natCast_re] at hr
      have : (0 : ℝ) ≤ Module.finrank ℂ (V i) := Nat.cast_nonneg _
      linarith
  refine ⟨V i, hS i, funext fun g => ?_⟩
  rw [heq, hc, Int.cast_one, one_mul]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory

set_option maxHeartbeats 400000

theorem g32p_simple_family (G : Type) [Group G] [Fintype G] :
    ∃ (Idx : Type) (_ : Fintype Idx) (σ : Idx → FDRep ℂ G), (∀ i, Simple (σ i)) ∧
      (∀ i j, Nonempty (σ i ≅ σ j) → i = j) ∧
      ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i) := by
  classical
  let S : Set (G → ℂ) := {f | ∃ τ : FDRep ℂ G, Simple τ ∧ τ.character = f}
  let σ : S → FDRep ℂ G := fun i => i.2.choose
  have hσ : ∀ i, Simple (σ i) := fun i => i.2.choose_spec.1
  have hχ : ∀ i, (σ i).character = i.1 := fun i => i.2.choose_spec.2
  have horth : ∀ i j : S, (Nat.card G : ℂ)⁻¹ * ∑ g, (i : G → ℂ) g * (j : G → ℂ) g⁻¹ =
      if i = j then 1 else 0 := by
    intro i j
    have := hσ i
    have := hσ j
    rw [← hχ i, ← hχ j, FDRep.char_orthonormal]
    congr 1
    refine propext ⟨fun ⟨e⟩ => Subtype.ext ?_, fun hij => hij ▸ ⟨Iso.refl _⟩⟩
    rw [← hχ i, ← hχ j]
    exact FDRep.char_iso e
  have hli : LinearIndependent ℂ (fun x : S => (x : G → ℂ)) := by
    rw [linearIndependent_iff']
    intro s c hc j hj
    have hpair := congrArg (fun f : G → ℂ => (Nat.card G : ℂ)⁻¹ * ∑ g, f g * (j : G → ℂ) g⁻¹) hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, mul_zero, Finset.sum_mul] at hpair
    rw [Finset.sum_comm, Finset.mul_sum] at hpair
    have hterm : ∀ i ∈ s, (Nat.card G : ℂ)⁻¹ * ∑ g, c i * (i : G → ℂ) g * (j : G → ℂ) g⁻¹ =
        if i = j then c i else 0 := by
      intro i _
      simp_rw [mul_assoc, ← Finset.mul_sum, mul_left_comm, horth, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j] at hpair
    simpa [hj] using hpair
  have hfin : S.Finite := hli.setFinite
  refine ⟨S, hfin.fintype, σ, hσ, fun i j ⟨e⟩ => Subtype.ext ?_, fun τ hτ => ?_⟩
  · rw [← hχ i, ← hχ j]
    exact FDRep.char_iso e
  · refine ⟨⟨τ.character, τ, hτ, rfl⟩, ?_⟩
    have := hσ ⟨τ.character, τ, hτ, rfl⟩
    exact g32p_simple_iso_of_character_eq _ _ (hχ ⟨τ.character, τ, hτ, rfl⟩).symm


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory
open scoped MonoidAlgebra Classical

set_option maxHeartbeats 400000

theorem g32p_trace_pi {I : Type} [Fintype I] (M : I → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, Module.Finite ℂ (M i)] (f : (∀ i, M i) →ₗ[ℂ] (∀ i, M i)) :
    LinearMap.trace ℂ _ f = ∑ i, LinearMap.trace ℂ (M i)
      ((LinearMap.proj i).comp (f.comp (LinearMap.single ℂ M i))) := by
  classical
  have hid : (LinearMap.id : (∀ i, M i) →ₗ[ℂ] (∀ i, M i)) =
      ∑ i, (LinearMap.single ℂ M i).comp (LinearMap.proj i) := by
    ext x j
    simp
  conv_lhs => rw [← LinearMap.comp_id f, hid]
  have hs : f.comp (∑ i, (LinearMap.single ℂ M i).comp (LinearMap.proj i)) =
      ∑ i, f.comp ((LinearMap.single ℂ M i).comp (LinearMap.proj i)) := by
    ext x j
    simp
  rw [hs, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory
open scoped MonoidAlgebra Classical

set_option maxHeartbeats 400000

def g32p_restrictScalarsEquiv {G M : Type} [Group G] [AddCommGroup M]
    [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] :
    RestrictScalars ℂ ℂ[G] M ≃ₗ[ℂ] M where
  __ := RestrictScalars.addEquiv ℂ ℂ[G] M
  map_smul' r x := by
    exact IsScalarTower.algebraMap_smul ℂ[G] r (RestrictScalars.addEquiv ℂ ℂ[G] M x)

set_option backward.isDefEq.respectTransparency false in
theorem g32p_simple_of_module {G M : Type} [Group G] [Fintype G] [AddCommGroup M]
    [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M]
    [Module.Finite ℂ M] [IsSimpleModule ℂ[G] M] :
    Simple (FDRep.of (Representation.ofModule' (k := ℂ) (G := G) M)) := by
  classical
  letI : Module ℂ (RestrictScalars ℂ ℂ[G] M) := RestrictScalars.module ℂ ℂ[G] M
  let e := g32p_restrictScalarsEquiv (G := G) (M := M)
  letI : Module.Finite ℂ (RestrictScalars ℂ ℂ[G] M) := Module.Finite.equiv (R := ℂ) e.symm
  let ρ : Representation ℂ G (RestrictScalars ℂ ℂ[G] M) := Representation.ofModule (k := ℂ) (G := G) M
  letI : Representation.IsIrreducible ρ :=
    (Representation.isSimpleModule_iff_irreducible_ofModule (k := ℂ) (G := G) M).mp inferInstance
  letI := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  have hc (g : G) : (Representation.ofModule' (k := ℂ) (G := G) M).character g =
      ρ.character g := by
    change LinearMap.trace ℂ M _ = LinearMap.trace ℂ _ _
    rw [← LinearMap.trace_conj' (ρ g) e]
    congr 1
  rw [FDRep.simple_iff_char_is_norm_one]
  change ∑ g, (Representation.ofModule' (k := ℂ) (G := G) M).character g *
    (Representation.ofModule' (k := ℂ) (G := G) M).character g⁻¹ = _
  simp_rw [hc]
  have h := Representation.char_orthonormal ρ ρ
  rw [ite_eq_left ⟨Representation.Equiv.refl ρ⟩] at h
  exact ((inv_mul_eq_one₀ (NeZero.ne (Nat.card G : ℂ))).mp h).symm

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory
open scoped MonoidAlgebra Classical

set_option maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false in
theorem g32p_character_decomposition {G : Type} [Group G] [Fintype G]
    (V : FDRep ℂ G) :
    ∃ (n : ℕ) (W : Fin n → FDRep ℂ G), (∀ i, Simple (W i)) ∧
      ∀ g, V.character g = ∑ i, (W i).character g := by
  classical
  letI : Module.Finite ℂ[G] (Representation.asModule V.ρ) :=
    Module.Finite.of_restrictScalars_finite ℂ ℂ[G] _
  obtain ⟨n, S, e, hS⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp ℂ[G] (Representation.asModule V.ρ)
  letI : ∀ i : Fin n, Module.Finite ℂ (S i) := fun i =>
    Module.Finite.of_injective ((S i).subtype.restrictScalars ℂ) (S i).subtype_injective
  let W (i : Fin n) := FDRep.of (Representation.ofModule' (k := ℂ) (G := G) (S i))
  have hW (i : Fin n) : Simple (W i) := by
    letI := hS i
    exact g32p_simple_of_module (G := G) (M := S i)
  let e' : (Representation.asModule V.ρ) ≃ₗ[ℂ[G]] (∀ i, S i) :=
    e.trans DFinsupp.linearEquivFunOnFintype
  let F : V ≃ₗ[ℂ] (∀ i, S i) :=
    (Representation.asModuleEquiv V.ρ).symm.trans (e'.restrictScalars ℂ)
  have hF (g : G) (x : V) : F (V.ρ g x) =
      fun i => (Representation.ofModule' (k := ℂ) (G := G) (S i)) g (F x i) := by
    change e' ((Representation.asModuleEquiv V.ρ).symm (V.ρ g x)) = _
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul]
    rfl
  refine ⟨n, W, hW, fun g => ?_⟩
  change LinearMap.trace ℂ V (V.ρ g) = _
  rw [← LinearMap.trace_conj' (V.ρ g) F, g32p_trace_pi]
  apply Finset.sum_congr rfl
  intro i _
  change LinearMap.trace ℂ (S i) _ = LinearMap.trace ℂ (S i) _
  congr 1
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.conj_apply_apply,
    LinearMap.single_apply]
  rw [hF, F.apply_symm_apply]
  simp only [Pi.single_eq_same]
  rfl

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory
open scoped Classical

set_option maxHeartbeats 400000

theorem g32p_character_mem_simple_span {G I : Type} [Group G] [Fintype G]
    (S : I → FDRep ℂ G)
    (hcov : ∀ W : FDRep ℂ G, Simple W → ∃ i, Nonempty (W ≅ S i))
    (V : FDRep ℂ G) :
    V.character ∈ Submodule.span ℂ (Set.range fun i => (S i).character) := by
  obtain ⟨n, W, hW, he⟩ := g32p_character_decomposition V
  have he' : V.character = ∑ j, (W j).character := by
    funext g
    simpa only [Finset.sum_apply] using he g
  rw [he']
  apply Submodule.sum_mem
  intro j _
  obtain ⟨i, ⟨e⟩⟩ := hcov (W j) (hW j)
  rw [FDRep.char_iso e]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem g32p_character_simple_expansion {G I : Type} [Group G] [Fintype G] [Fintype I]
    (S : I → FDRep ℂ G) (hS : ∀ i, Simple (S i))
    (hN : ∀ i j, i ≠ j → IsEmpty (S i ≅ S j))
    (hcov : ∀ W : FDRep ℂ G, Simple W → ∃ i, Nonempty (W ≅ S i))
    (V : FDRep ℂ G) (g : G) :
    V.character g = ∑ i, (Module.finrank ℂ (S i ⟶ V) : ℂ) * (S i).character g := by
  classical
  letI : ∀ i, Simple (S i) := hS
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (g32p_character_mem_simple_span S hcov V)
  have hp (i j : I) : g32p_characterPairing (S i) (S j).character =
      if j = i then 1 else 0 := by
    rw [g32p_characterPairing_simple]
    split_ifs with h hi
    · rfl
    · exact False.elim ((hN j i hi).false h.some)
    · subst j
      exact False.elim (h ⟨Iso.refl _⟩)
    · rfl
  have hm (i : I) : c i = (Module.finrank ℂ (S i ⟶ V) : ℂ) := by
    have h := congrArg (g32p_characterPairing (S i)) hc
    simp only [map_sum, map_smul, hp, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    rw [h]
    exact FDRep.scalar_product_char_eq_finrank_equivariant (S i) V
  have h := congrFun hc g
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm] using h.symm

theorem g32p_realize_virtual_character {G K : Type} [Group G] [Fintype G] [Fintype K]
    (V : K → FDRep ℂ G) (a : K → ℤ) (f : G → ℂ)
    (hf : ∀ g, f g = ∑ k, (a k : ℂ) * (V k).character g)
    (hnorm : (Nat.card G : ℂ)⁻¹ * ∑ g, f g * f g⁻¹ = 1)
    (hpos : 0 < (f 1).re) :
    ∃ W : FDRep ℂ G, Simple W ∧ W.character = f := by
  classical
  obtain ⟨I, _, S, hS, hN, hcov⟩ := g32p_simple_family G
  have hN' (i j : I) (hij : i ≠ j) : IsEmpty (S i ≅ S j) :=
    ⟨fun e => hij (hN i j ⟨e⟩)⟩
  let c (i : I) : ℤ := ∑ k, a k * (Module.finrank ℂ (S i ⟶ V k) : ℤ)
  apply g32p_realize_simple_integer_expansion S hS hN' c f ?_ hnorm hpos
  intro g
  rw [hf]
  have hv (k : K) := g32p_character_simple_expansion S hS hN' hcov (V k) g
  simp_rw [hv, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [c, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

end HodgeLean.Foundations.Program

end
end
