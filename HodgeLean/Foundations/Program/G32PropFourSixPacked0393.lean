import HodgeLean.Foundations.Program.G32PropFourSixPacked0392
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow24
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

theorem g32p_row23_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row23_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row23_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
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

theorem g32p_row23_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row23_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row23_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row23_variantArithmetic_00_0 r
  · exact g32p_row23_variantArithmetic_01_0 r
  · exact g32p_row23_variantArithmetic_02_0 r
  · exact g32p_row23_variantArithmetic_03_0 r
  · exact g32p_row23_variantArithmetic_04_0 r
  · exact g32p_row23_variantArithmetic_05_0 r
  · exact g32p_row23_variantArithmetic_06_0 r

theorem g32p_row23_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row23_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row23_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row23_variantArithmetic_00_1 r
  · exact g32p_row23_variantArithmetic_01_1 r
  · exact g32p_row23_variantArithmetic_02_1 r
  · exact g32p_row23_variantArithmetic_03_1 r
  · exact g32p_row23_variantArithmetic_04_1 r
  · exact g32p_row23_variantArithmetic_05_1 r
  · exact g32p_row23_variantArithmetic_06_1 r

theorem g32p_row23_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row23_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row23_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row23_variantArithmetic_00_2 r
  · exact g32p_row23_variantArithmetic_01_2 r
  · exact g32p_row23_variantArithmetic_02_2 r
  · exact g32p_row23_variantArithmetic_03_2 r
  · exact g32p_row23_variantArithmetic_04_2 r
  · exact g32p_row23_variantArithmetic_05_2 r
  · exact g32p_row23_variantArithmetic_06_2 r

theorem g32p_row23_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row23_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row23_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row23_variantArithmetic_00_3 r
  · exact g32p_row23_variantArithmetic_01_3 r
  · exact g32p_row23_variantArithmetic_02_3 r
  · exact g32p_row23_variantArithmetic_03_3 r
  · exact g32p_row23_variantArithmetic_04_3 r
  · exact g32p_row23_variantArithmetic_05_3 r
  · exact g32p_row23_variantArithmetic_06_3 r

theorem g32p_row23_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row23_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row23_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row23_variantArithmetic_00_4 r
  · exact g32p_row23_variantArithmetic_01_4 r
  · exact g32p_row23_variantArithmetic_02_4 r
  · exact g32p_row23_variantArithmetic_03_4 r
  · exact g32p_row23_variantArithmetic_04_4 r
  · exact g32p_row23_variantArithmetic_05_4 r
  · exact g32p_row23_variantArithmetic_06_4 r

theorem g32p_row23_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row23_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row23_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row23_variantArithmetic_00_5 r
  · exact g32p_row23_variantArithmetic_01_5 r
  · exact g32p_row23_variantArithmetic_02_5 r
  · exact g32p_row23_variantArithmetic_03_5 r
  · exact g32p_row23_variantArithmetic_04_5 r
  · exact g32p_row23_variantArithmetic_05_5 r
  · exact g32p_row23_variantArithmetic_06_5 r

theorem g32p_row23_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row23_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row23_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row23_variantArithmetic_00_6 r
  · exact g32p_row23_variantArithmetic_01_6 r
  · exact g32p_row23_variantArithmetic_02_6 r
  · exact g32p_row23_variantArithmetic_03_6 r
  · exact g32p_row23_variantArithmetic_04_6 r
  · exact g32p_row23_variantArithmetic_05_6 r
  · exact g32p_row23_variantArithmetic_06_6 r

theorem g32p_row23_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row23_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row23_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 22 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row23_variantArithmetic_00_7 r
  · exact g32p_row23_variantArithmetic_01_7 r
  · exact g32p_row23_variantArithmetic_02_7 r
  · exact g32p_row23_variantArithmetic_03_7 r
  · exact g32p_row23_variantArithmetic_04_7 r
  · exact g32p_row23_variantArithmetic_05_7 r
  · exact g32p_row23_variantArithmetic_06_7 r

theorem g32p_row23_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row23_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row23_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 22 c _ (g32p_row23_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row23_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 22 c _ (g32p_row23_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row23_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 22 c _ (g32p_row23_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row23_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 22 c _ (g32p_row23_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row23_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 22 c _ (g32p_row23_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row23_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 22 c _ (g32p_row23_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row23_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 22 c _ (g32p_row23_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row23_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 22 c _ (g32p_row23_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row23_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup19_source : Fin 1152 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 576 then (if i.val < 288 then (if i.val < 144 then (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (76, 135)) else (if i.val < 3 then (65, 234) else (86, 35))) else (if i.val < 6 then (if i.val < 5 then (21, 88) else (0, 97)) else (if i.val < 7 then (52, 76) else (if i.val < 8 then (38, 66) else (63, 25))))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then (111, 173) else (0, 99)) else (if i.val < 12 then (11, 8) else (134, 184))) else (if i.val < 15 then (if i.val < 14 then (79, 145) else (66, 51)) else (if i.val < 16 then (86, 110) else (if i.val < 17 then (5, 217) else (134, 124)))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then (117, 118) else (0, 18)) else (if i.val < 21 then (3, 239) else (17, 84))) else (if i.val < 24 then (if i.val < 23 then (24, 249) else (130, 144)) else (if i.val < 25 then (59, 7) else (if i.val < 26 then (9, 205) else (115, 61))))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then (124, 245) else (72, 3)) else (if i.val < 30 then (20, 172) else (85, 185))) else (if i.val < 33 then (if i.val < 32 then (105, 93) else (73, 27)) else (if i.val < 34 then (115, 106) else (if i.val < 35 then (49, 87) else (63, 93))))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then (107, 65) else (125, 222)) else (if i.val < 39 then (13, 253) else (82, 200))) else (if i.val < 42 then (if i.val < 41 then (95, 221) else (116, 39)) else (if i.val < 43 then (81, 195) else (if i.val < 44 then (39, 25) else (40, 140))))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then (140, 29) else (23, 205)) else (if i.val < 48 then (108, 45) else (60, 119))) else (if i.val < 51 then (if i.val < 50 then (20, 191) else (37, 19)) else (if i.val < 52 then (80, 104) else (if i.val < 53 then (96, 172) else (117, 109)))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then (36, 26) else (112, 159)) else (if i.val < 57 then (106, 234) else (4, 97))) else (if i.val < 60 then (if i.val < 59 then (126, 52) else (144, 52)) else (if i.val < 61 then (76, 16) else (if i.val < 62 then (104, 0) else (40, 178))))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then (40, 179) else (36, 250)) else (if i.val < 66 then (39, 202) else (0, 101))) else (if i.val < 69 then (if i.val < 68 then (53, 58) else (41, 60)) else (if i.val < 70 then (144, 206) else (if i.val < 71 then (30, 171) else (0, 96)))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then (11, 132) else (114, 137)) else (if i.val < 75 then (108, 85) else (74, 132))) else (if i.val < 78 then (if i.val < 77 then (4, 192) else (99, 149)) else (if i.val < 79 then (21, 197) else (if i.val < 80 then (59, 66) else (25, 236))))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then (11, 228) else (55, 214)) else (if i.val < 84 then (141, 183) else (36, 74))) else (if i.val < 87 then (if i.val < 86 then (20, 122) else (88, 218)) else (if i.val < 88 then (99, 96) else (if i.val < 89 then (126, 120) else (28, 221)))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then (128, 71) else (113, 226)) else (if i.val < 93 then (116, 176) else (139, 154))) else (if i.val < 96 then (if i.val < 95 then (98, 57) else (138, 53)) else (if i.val < 97 then (98, 113) else (if i.val < 98 then (102, 48) else (114, 222))))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then (133, 200) else (74, 141)) else (if i.val < 102 then (107, 57) else (73, 20))) else (if i.val < 105 then (if i.val < 104 then (133, 84) else (113, 243)) else (if i.val < 106 then (97, 22) else (if i.val < 107 then (98, 191) else (142, 91))))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then (37, 98) else (63, 1)) else (if i.val < 111 then (1, 111) else (133, 44))) else (if i.val < 114 then (if i.val < 113 then (32, 43) else (105, 121)) else (if i.val < 115 then (139, 64) else (if i.val < 116 then (131, 21) else (60, 68))))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then (127, 58) else (127, 36)) else (if i.val < 120 then (113, 208) else (61, 231))) else (if i.val < 123 then (if i.val < 122 then (106, 250) else (112, 165)) else (if i.val < 124 then (143, 13) else (if i.val < 125 then (85, 186) else (95, 24)))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then (82, 136) else (82, 254)) else (if i.val < 129 then (133, 55) else (118, 72))) else (if i.val < 132 then (if i.val < 131 then (83, 30) else (61, 192)) else (if i.val < 133 then (115, 52) else (if i.val < 134 then (36, 146) else (126, 227))))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then (118, 184) else (104, 54)) else (if i.val < 138 then (94, 22) else (90, 183))) else (if i.val < 141 then (if i.val < 140 then (116, 192) else (102, 127)) else (if i.val < 142 then (48, 254) else (if i.val < 143 then (89, 206) else (53, 249))))))))) else (if i.val < 216 then (if i.val < 180 then (if i.val < 162 then (if i.val < 153 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then (67, 74) else (115, 220)) else (if i.val < 147 then (55, 4) else (20, 187))) else (if i.val < 150 then (if i.val < 149 then (140, 96) else (25, 0)) else (if i.val < 151 then (90, 38) else (if i.val < 152 then (9, 93) else (77, 56))))) else (if i.val < 157 then (if i.val < 155 then (if i.val < 154 then (88, 147) else (105, 14)) else (if i.val < 156 then (80, 81) else (126, 216))) else (if i.val < 159 then (if i.val < 158 then (32, 115) else (142, 204)) else (if i.val < 160 then (28, 255) else (if i.val < 161 then (76, 144) else (144, 90)))))) else (if i.val < 171 then (if i.val < 166 then (if i.val < 164 then (if i.val < 163 then (126, 237) else (5, 80)) else (if i.val < 165 then (42, 191) else (90, 211))) else (if i.val < 168 then (if i.val < 167 then (50, 89) else (35, 217)) else (if i.val < 169 then (141, 196) else (if i.val < 170 then (84, 196) else (140, 64))))) else (if i.val < 175 then (if i.val < 173 then (if i.val < 172 then (127, 164) else (134, 116)) else (if i.val < 174 then (49, 113) else (38, 229))) else (if i.val < 177 then (if i.val < 176 then (100, 53) else (63, 240)) else (if i.val < 178 then (103, 238) else (if i.val < 179 then (50, 154) else (111, 208))))))) else (if i.val < 198 then (if i.val < 189 then (if i.val < 184 then (if i.val < 182 then (if i.val < 181 then (118, 67) else (140, 243)) else (if i.val < 183 then (119, 83) else (49, 236))) else (if i.val < 186 then (if i.val < 185 then (42, 225) else (39, 229)) else (if i.val < 187 then (127, 245) else (if i.val < 188 then (126, 15) else (78, 135))))) else (if i.val < 193 then (if i.val < 191 then (if i.val < 190 then (105, 160) else (109, 70)) else (if i.val < 192 then (59, 1) else (9, 97))) else (if i.val < 195 then (if i.val < 194 then (128, 38) else (111, 160)) else (if i.val < 196 then (28, 96) else (if i.val < 197 then (42, 39) else (66, 119)))))) else (if i.val < 207 then (if i.val < 202 then (if i.val < 200 then (if i.val < 199 then (96, 104) else (63, 246)) else (if i.val < 201 then (22, 153) else (85, 117))) else (if i.val < 204 then (if i.val < 203 then (144, 200) else (144, 149)) else (if i.val < 205 then (52, 135) else (if i.val < 206 then (53, 19) else (108, 152))))) else (if i.val < 211 then (if i.val < 209 then (if i.val < 208 then (128, 185) else (48, 65)) else (if i.val < 210 then (70, 159) else (5, 148))) else (if i.val < 213 then (if i.val < 212 then (130, 81) else (83, 197)) else (if i.val < 214 then (98, 12) else (if i.val < 215 then (12, 41) else (86, 184)))))))) else (if i.val < 252 then (if i.val < 234 then (if i.val < 225 then (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then (4, 191) else (143, 123)) else (if i.val < 219 then (94, 88) else (68, 130))) else (if i.val < 222 then (if i.val < 221 then (33, 52) else (4, 107)) else (if i.val < 223 then (110, 131) else (if i.val < 224 then (136, 220) else (92, 239))))) else (if i.val < 229 then (if i.val < 227 then (if i.val < 226 then (11, 216) else (140, 247)) else (if i.val < 228 then (12, 46) else (136, 26))) else (if i.val < 231 then (if i.val < 230 then (117, 182) else (65, 10)) else (if i.val < 232 then (81, 63) else (if i.val < 233 then (11, 250) else (17, 89)))))) else (if i.val < 243 then (if i.val < 238 then (if i.val < 236 then (if i.val < 235 then (33, 43) else (136, 189)) else (if i.val < 237 then (35, 13) else (131, 9))) else (if i.val < 240 then (if i.val < 239 then (45, 36) else (10, 151)) else (if i.val < 241 then (141, 145) else (if i.val < 242 then (5, 158) else (71, 32))))) else (if i.val < 247 then (if i.val < 245 then (if i.val < 244 then (143, 3) else (111, 90)) else (if i.val < 246 then (124, 113) else (79, 71))) else (if i.val < 249 then (if i.val < 248 then (104, 87) else (1, 120)) else (if i.val < 250 then (116, 211) else (if i.val < 251 then (25, 207) else (106, 223))))))) else (if i.val < 270 then (if i.val < 261 then (if i.val < 256 then (if i.val < 254 then (if i.val < 253 then (84, 118) else (30, 211)) else (if i.val < 255 then (47, 247) else (47, 146))) else (if i.val < 258 then (if i.val < 257 then (138, 248) else (74, 244)) else (if i.val < 259 then (105, 179) else (if i.val < 260 then (12, 84) else (83, 225))))) else (if i.val < 265 then (if i.val < 263 then (if i.val < 262 then (100, 29) else (72, 48)) else (if i.val < 264 then (25, 135) else (51, 173))) else (if i.val < 267 then (if i.val < 266 then (8, 37) else (52, 213)) else (if i.val < 268 then (24, 155) else (if i.val < 269 then (137, 151) else (69, 252)))))) else (if i.val < 279 then (if i.val < 274 then (if i.val < 272 then (if i.val < 271 then (122, 146) else (111, 30)) else (if i.val < 273 then (74, 120) else (47, 242))) else (if i.val < 276 then (if i.val < 275 then (24, 84) else (132, 244)) else (if i.val < 277 then (14, 138) else (if i.val < 278 then (73, 250) else (102, 51))))) else (if i.val < 283 then (if i.val < 281 then (if i.val < 280 then (71, 105) else (80, 6)) else (if i.val < 282 then (47, 47) else (44, 232))) else (if i.val < 285 then (if i.val < 284 then (11, 164) else (72, 86)) else (if i.val < 286 then (117, 251) else (if i.val < 287 then (133, 8) else (100, 161)))))))))) else (if i.val < 432 then (if i.val < 360 then (if i.val < 324 then (if i.val < 306 then (if i.val < 297 then (if i.val < 292 then (if i.val < 290 then (if i.val < 289 then (100, 34) else (99, 143)) else (if i.val < 291 then (72, 94) else (68, 5))) else (if i.val < 294 then (if i.val < 293 then (26, 128) else (47, 166)) else (if i.val < 295 then (124, 155) else (if i.val < 296 then (120, 209) else (62, 62))))) else (if i.val < 301 then (if i.val < 299 then (if i.val < 298 then (19, 27) else (38, 191)) else (if i.val < 300 then (47, 103) else (19, 62))) else (if i.val < 303 then (if i.val < 302 then (37, 99) else (74, 236)) else (if i.val < 304 then (24, 247) else (if i.val < 305 then (71, 9) else (132, 107)))))) else (if i.val < 315 then (if i.val < 310 then (if i.val < 308 then (if i.val < 307 then (127, 135) else (51, 247)) else (if i.val < 309 then (19, 81) else (116, 50))) else (if i.val < 312 then (if i.val < 311 then (79, 207) else (105, 69)) else (if i.val < 313 then (134, 78) else (if i.val < 314 then (0, 153) else (139, 52))))) else (if i.val < 319 then (if i.val < 317 then (if i.val < 316 then (77, 45) else (26, 179)) else (if i.val < 318 then (143, 151) else (89, 211))) else (if i.val < 321 then (if i.val < 320 then (126, 246) else (99, 188)) else (if i.val < 322 then (80, 34) else (if i.val < 323 then (126, 39) else (25, 70))))))) else (if i.val < 342 then (if i.val < 333 then (if i.val < 328 then (if i.val < 326 then (if i.val < 325 then (132, 103) else (24, 192)) else (if i.val < 327 then (7, 171) else (114, 172))) else (if i.val < 330 then (if i.val < 329 then (32, 78) else (142, 71)) else (if i.val < 331 then (51, 26) else (if i.val < 332 then (106, 142) else (81, 248))))) else (if i.val < 337 then (if i.val < 335 then (if i.val < 334 then (89, 154) else (22, 234)) else (if i.val < 336 then (105, 178) else (19, 92))) else (if i.val < 339 then (if i.val < 338 then (62, 172) else (114, 179)) else (if i.val < 340 then (124, 206) else (if i.val < 341 then (9, 137) else (79, 54)))))) else (if i.val < 351 then (if i.val < 346 then (if i.val < 344 then (if i.val < 343 then (142, 215) else (75, 52)) else (if i.val < 345 then (133, 185) else (132, 245))) else (if i.val < 348 then (if i.val < 347 then (63, 43) else (106, 171)) else (if i.val < 349 then (140, 42) else (if i.val < 350 then (133, 81) else (80, 66))))) else (if i.val < 355 then (if i.val < 353 then (if i.val < 352 then (27, 173) else (77, 151)) else (if i.val < 354 then (104, 4) else (90, 146))) else (if i.val < 357 then (if i.val < 356 then (114, 168) else (48, 215)) else (if i.val < 358 then (5, 205) else (if i.val < 359 then (80, 131) else (133, 43)))))))) else (if i.val < 396 then (if i.val < 378 then (if i.val < 369 then (if i.val < 364 then (if i.val < 362 then (if i.val < 361 then (79, 251) else (126, 86)) else (if i.val < 363 then (71, 5) else (116, 125))) else (if i.val < 366 then (if i.val < 365 then (9, 60) else (15, 91)) else (if i.val < 367 then (105, 215) else (if i.val < 368 then (38, 79) else (18, 177))))) else (if i.val < 373 then (if i.val < 371 then (if i.val < 370 then (9, 108) else (130, 206)) else (if i.val < 372 then (124, 55) else (84, 171))) else (if i.val < 375 then (if i.val < 374 then (144, 185) else (105, 209)) else (if i.val < 376 then (84, 52) else (if i.val < 377 then (74, 105) else (11, 155)))))) else (if i.val < 387 then (if i.val < 382 then (if i.val < 380 then (if i.val < 379 then (72, 76) else (144, 223)) else (if i.val < 381 then (110, 101) else (136, 250))) else (if i.val < 384 then (if i.val < 383 then (48, 7) else (105, 123)) else (if i.val < 385 then (77, 130) else (if i.val < 386 then (12, 4) else (56, 57))))) else (if i.val < 391 then (if i.val < 389 then (if i.val < 388 then (28, 35) else (140, 73)) else (if i.val < 390 then (101, 187) else (91, 209))) else (if i.val < 393 then (if i.val < 392 then (76, 34) else (78, 233)) else (if i.val < 394 then (60, 136) else (if i.val < 395 then (133, 153) else (131, 144))))))) else (if i.val < 414 then (if i.val < 405 then (if i.val < 400 then (if i.val < 398 then (if i.val < 397 then (60, 155) else (104, 6)) else (if i.val < 399 then (111, 108) else (80, 151))) else (if i.val < 402 then (if i.val < 401 then (134, 132) else (58, 199)) else (if i.val < 403 then (127, 201) else (if i.val < 404 then (13, 64) else (106, 82))))) else (if i.val < 409 then (if i.val < 407 then (if i.val < 406 then (49, 75) else (111, 188)) else (if i.val < 408 then (144, 28) else (28, 188))) else (if i.val < 411 then (if i.val < 410 then (103, 147) else (8, 160)) else (if i.val < 412 then (77, 20) else (if i.val < 413 then (74, 28) else (112, 77)))))) else (if i.val < 423 then (if i.val < 418 then (if i.val < 416 then (if i.val < 415 then (139, 161) else (126, 65)) else (if i.val < 417 then (126, 159) else (43, 227))) else (if i.val < 420 then (if i.val < 419 then (70, 192) else (58, 235)) else (if i.val < 421 then (138, 33) else (if i.val < 422 then (28, 166) else (123, 172))))) else (if i.val < 427 then (if i.val < 425 then (if i.val < 424 then (124, 1) else (24, 131)) else (if i.val < 426 then (134, 80) else (63, 183))) else (if i.val < 429 then (if i.val < 428 then (97, 177) else (127, 126)) else (if i.val < 430 then (125, 186) else (if i.val < 431 then (104, 60) else (91, 43))))))))) else (if i.val < 504 then (if i.val < 468 then (if i.val < 450 then (if i.val < 441 then (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then (123, 146) else (11, 156)) else (if i.val < 435 then (47, 130) else (140, 74))) else (if i.val < 438 then (if i.val < 437 then (36, 231) else (113, 130)) else (if i.val < 439 then (26, 182) else (if i.val < 440 then (0, 37) else (85, 187))))) else (if i.val < 445 then (if i.val < 443 then (if i.val < 442 then (115, 125) else (99, 95)) else (if i.val < 444 then (62, 76) else (128, 28))) else (if i.val < 447 then (if i.val < 446 then (85, 71) else (133, 183)) else (if i.val < 448 then (85, 84) else (if i.val < 449 then (37, 154) else (105, 248)))))) else (if i.val < 459 then (if i.val < 454 then (if i.val < 452 then (if i.val < 451 then (139, 39) else (57, 206)) else (if i.val < 453 then (67, 169) else (134, 136))) else (if i.val < 456 then (if i.val < 455 then (89, 93) else (16, 144)) else (if i.val < 457 then (65, 124) else (if i.val < 458 then (129, 142) else (120, 70))))) else (if i.val < 463 then (if i.val < 461 then (if i.val < 460 then (141, 33) else (36, 151)) else (if i.val < 462 then (66, 146) else (144, 104))) else (if i.val < 465 then (if i.val < 464 then (86, 85) else (134, 196)) else (if i.val < 466 then (114, 188) else (if i.val < 467 then (109, 117) else (109, 228))))))) else (if i.val < 486 then (if i.val < 477 then (if i.val < 472 then (if i.val < 470 then (if i.val < 469 then (0, 65) else (143, 17)) else (if i.val < 471 then (33, 21) else (86, 97))) else (if i.val < 474 then (if i.val < 473 then (22, 83) else (6, 200)) else (if i.val < 475 then (68, 241) else (if i.val < 476 then (119, 237) else (23, 208))))) else (if i.val < 481 then (if i.val < 479 then (if i.val < 478 then (53, 20) else (46, 203)) else (if i.val < 480 then (99, 227) else (85, 116))) else (if i.val < 483 then (if i.val < 482 then (55, 75) else (92, 252)) else (if i.val < 484 then (99, 77) else (if i.val < 485 then (40, 67) else (109, 67)))))) else (if i.val < 495 then (if i.val < 490 then (if i.val < 488 then (if i.val < 487 then (82, 102) else (119, 107)) else (if i.val < 489 then (60, 51) else (94, 96))) else (if i.val < 492 then (if i.val < 491 then (100, 251) else (112, 242)) else (if i.val < 493 then (136, 105) else (if i.val < 494 then (118, 129) else (66, 161))))) else (if i.val < 499 then (if i.val < 497 then (if i.val < 496 then (95, 123) else (96, 251)) else (if i.val < 498 then (33, 18) else (79, 73))) else (if i.val < 501 then (if i.val < 500 then (93, 109) else (68, 198)) else (if i.val < 502 then (118, 246) else (if i.val < 503 then (107, 166) else (113, 15)))))))) else (if i.val < 540 then (if i.val < 522 then (if i.val < 513 then (if i.val < 508 then (if i.val < 506 then (if i.val < 505 then (107, 145) else (141, 1)) else (if i.val < 507 then (140, 171) else (64, 88))) else (if i.val < 510 then (if i.val < 509 then (40, 66) else (80, 192)) else (if i.val < 511 then (128, 165) else (if i.val < 512 then (120, 107) else (72, 24))))) else (if i.val < 517 then (if i.val < 515 then (if i.val < 514 then (120, 56) else (53, 128)) else (if i.val < 516 then (92, 31) else (109, 157))) else (if i.val < 519 then (if i.val < 518 then (104, 20) else (129, 249)) else (if i.val < 520 then (128, 110) else (if i.val < 521 then (144, 125) else (53, 123)))))) else (if i.val < 531 then (if i.val < 526 then (if i.val < 524 then (if i.val < 523 then (41, 38) else (14, 88)) else (if i.val < 525 then (135, 124) else (135, 245))) else (if i.val < 528 then (if i.val < 527 then (54, 177) else (143, 190)) else (if i.val < 529 then (121, 178) else (if i.val < 530 then (41, 5) else (98, 99))))) else (if i.val < 535 then (if i.val < 533 then (if i.val < 532 then (44, 237) else (143, 102)) else (if i.val < 534 then (140, 226) else (29, 147))) else (if i.val < 537 then (if i.val < 536 then (129, 244) else (144, 218)) else (if i.val < 538 then (73, 95) else (if i.val < 539 then (88, 61) else (4, 108))))))) else (if i.val < 558 then (if i.val < 549 then (if i.val < 544 then (if i.val < 542 then (if i.val < 541 then (56, 225) else (113, 133)) else (if i.val < 543 then (34, 8) else (140, 160))) else (if i.val < 546 then (if i.val < 545 then (72, 176) else (6, 195)) else (if i.val < 547 then (2, 129) else (if i.val < 548 then (124, 159) else (40, 25))))) else (if i.val < 553 then (if i.val < 551 then (if i.val < 550 then (56, 224) else (73, 157)) else (if i.val < 552 then (21, 73) else (119, 11))) else (if i.val < 555 then (if i.val < 554 then (65, 147) else (117, 78)) else (if i.val < 556 then (26, 34) else (if i.val < 557 then (142, 1) else (71, 58)))))) else (if i.val < 567 then (if i.val < 562 then (if i.val < 560 then (if i.val < 559 then (24, 210) else (61, 101)) else (if i.val < 561 then (131, 49) else (48, 228))) else (if i.val < 564 then (if i.val < 563 then (99, 7) else (100, 218)) else (if i.val < 565 then (131, 27) else (if i.val < 566 then (110, 52) else (45, 139))))) else (if i.val < 571 then (if i.val < 569 then (if i.val < 568 then (122, 69) else (120, 181)) else (if i.val < 570 then (73, 142) else (67, 54))) else (if i.val < 573 then (if i.val < 572 then (87, 38) else (87, 43)) else (if i.val < 574 then (58, 115) else (if i.val < 575 then (123, 181) else (113, 120))))))))))) else (if i.val < 864 then (if i.val < 720 then (if i.val < 648 then (if i.val < 612 then (if i.val < 594 then (if i.val < 585 then (if i.val < 580 then (if i.val < 578 then (if i.val < 577 then (69, 213) else (120, 240)) else (if i.val < 579 then (101, 254) else (71, 98))) else (if i.val < 582 then (if i.val < 581 then (122, 198) else (72, 238)) else (if i.val < 583 then (92, 232) else (if i.val < 584 then (2, 16) else (142, 62))))) else (if i.val < 589 then (if i.val < 587 then (if i.val < 586 then (114, 4) else (64, 99)) else (if i.val < 588 then (73, 244) else (45, 90))) else (if i.val < 591 then (if i.val < 590 then (69, 109) else (58, 70)) else (if i.val < 592 then (65, 139) else (if i.val < 593 then (9, 215) else (123, 65)))))) else (if i.val < 603 then (if i.val < 598 then (if i.val < 596 then (if i.val < 595 then (107, 242) else (70, 26)) else (if i.val < 597 then (111, 58) else (138, 136))) else (if i.val < 600 then (if i.val < 599 then (132, 3) else (100, 195)) else (if i.val < 601 then (75, 104) else (if i.val < 602 then (137, 113) else (95, 252))))) else (if i.val < 607 then (if i.val < 605 then (if i.val < 604 then (124, 37) else (4, 128)) else (if i.val < 606 then (59, 185) else (124, 122))) else (if i.val < 609 then (if i.val < 608 then (138, 140) else (84, 160)) else (if i.val < 610 then (93, 124) else (if i.val < 611 then (7, 212) else (136, 244))))))) else (if i.val < 630 then (if i.val < 621 then (if i.val < 616 then (if i.val < 614 then (if i.val < 613 then (53, 59) else (71, 166)) else (if i.val < 615 then (99, 93) else (85, 142))) else (if i.val < 618 then (if i.val < 617 then (98, 89) else (72, 57)) else (if i.val < 619 then (136, 203) else (if i.val < 620 then (87, 115) else (141, 97))))) else (if i.val < 625 then (if i.val < 623 then (if i.val < 622 then (142, 81) else (87, 0)) else (if i.val < 624 then (17, 160) else (99, 59))) else (if i.val < 627 then (if i.val < 626 then (12, 101) else (108, 235)) else (if i.val < 628 then (32, 174) else (if i.val < 629 then (39, 193) else (117, 121)))))) else (if i.val < 639 then (if i.val < 634 then (if i.val < 632 then (if i.val < 631 then (114, 86) else (142, 227)) else (if i.val < 633 then (73, 194) else (55, 35))) else (if i.val < 636 then (if i.val < 635 then (93, 139) else (124, 145)) else (if i.val < 637 then (114, 90) else (if i.val < 638 then (47, 85) else (74, 13))))) else (if i.val < 643 then (if i.val < 641 then (if i.val < 640 then (4, 33) else (64, 10)) else (if i.val < 642 then (135, 207) else (33, 207))) else (if i.val < 645 then (if i.val < 644 then (138, 152) else (134, 48)) else (if i.val < 646 then (144, 198) else (if i.val < 647 then (56, 38) else (111, 8)))))))) else (if i.val < 684 then (if i.val < 666 then (if i.val < 657 then (if i.val < 652 then (if i.val < 650 then (if i.val < 649 then (139, 80) else (62, 124)) else (if i.val < 651 then (114, 58) else (34, 196))) else (if i.val < 654 then (if i.val < 653 then (20, 168) else (34, 124)) else (if i.val < 655 then (136, 194) else (if i.val < 656 then (101, 221) else (132, 168))))) else (if i.val < 661 then (if i.val < 659 then (if i.val < 658 then (134, 179) else (144, 4)) else (if i.val < 660 then (11, 127) else (38, 209))) else (if i.val < 663 then (if i.val < 662 then (133, 203) else (19, 168)) else (if i.val < 664 then (50, 174) else (if i.val < 665 then (62, 167) else (84, 37)))))) else (if i.val < 675 then (if i.val < 670 then (if i.val < 668 then (if i.val < 667 then (116, 11) else (19, 252)) else (if i.val < 669 then (104, 115) else (116, 37))) else (if i.val < 672 then (if i.val < 671 then (133, 45) else (89, 170)) else (if i.val < 673 then (20, 4) else (if i.val < 674 then (89, 69) else (90, 67))))) else (if i.val < 679 then (if i.val < 677 then (if i.val < 676 then (144, 199) else (143, 133)) else (if i.val < 678 then (36, 157) else (115, 216))) else (if i.val < 681 then (if i.val < 680 then (88, 213) else (57, 26)) else (if i.val < 682 then (101, 16) else (if i.val < 683 then (101, 171) else (44, 140))))))) else (if i.val < 702 then (if i.val < 693 then (if i.val < 688 then (if i.val < 686 then (if i.val < 685 then (88, 47) else (138, 121)) else (if i.val < 687 then (133, 5) else (102, 76))) else (if i.val < 690 then (if i.val < 689 then (51, 28) else (87, 178)) else (if i.val < 691 then (19, 207) else (if i.val < 692 then (142, 94) else (105, 36))))) else (if i.val < 697 then (if i.val < 695 then (if i.val < 694 then (20, 126) else (106, 213)) else (if i.val < 696 then (139, 125) else (2, 106))) else (if i.val < 699 then (if i.val < 698 then (76, 114) else (2, 103)) else (if i.val < 700 then (116, 164) else (if i.val < 701 then (15, 117) else (85, 194)))))) else (if i.val < 711 then (if i.val < 706 then (if i.val < 704 then (if i.val < 703 then (13, 14) else (60, 82)) else (if i.val < 705 then (15, 118) else (24, 28))) else (if i.val < 708 then (if i.val < 707 then (103, 117) else (137, 237)) else (if i.val < 709 then (112, 23) else (if i.val < 710 then (116, 209) else (50, 141))))) else (if i.val < 715 then (if i.val < 713 then (if i.val < 712 then (101, 179) else (87, 229)) else (if i.val < 714 then (16, 29) else (140, 185))) else (if i.val < 717 then (if i.val < 716 then (72, 146) else (47, 73)) else (if i.val < 718 then (114, 77) else (if i.val < 719 then (143, 180) else (71, 93))))))))) else (if i.val < 792 then (if i.val < 756 then (if i.val < 738 then (if i.val < 729 then (if i.val < 724 then (if i.val < 722 then (if i.val < 721 then (121, 133) else (58, 62)) else (if i.val < 723 then (102, 38) else (102, 103))) else (if i.val < 726 then (if i.val < 725 then (83, 191) else (137, 196)) else (if i.val < 727 then (111, 118) else (if i.val < 728 then (35, 6) else (12, 120))))) else (if i.val < 733 then (if i.val < 731 then (if i.val < 730 then (54, 126) else (132, 123)) else (if i.val < 732 then (58, 75) else (111, 99))) else (if i.val < 735 then (if i.val < 734 then (73, 0) else (1, 85)) else (if i.val < 736 then (26, 97) else (if i.val < 737 then (86, 254) else (45, 186)))))) else (if i.val < 747 then (if i.val < 742 then (if i.val < 740 then (if i.val < 739 then (122, 77) else (75, 153)) else (if i.val < 741 then (143, 119) else (113, 135))) else (if i.val < 744 then (if i.val < 743 then (122, 212) else (45, 126)) else (if i.val < 745 then (139, 47) else (if i.val < 746 then (90, 59) else (142, 195))))) else (if i.val < 751 then (if i.val < 749 then (if i.val < 748 then (100, 166) else (15, 170)) else (if i.val < 750 then (138, 124) else (114, 49))) else (if i.val < 753 then (if i.val < 752 then (125, 203) else (75, 181)) else (if i.val < 754 then (111, 124) else (if i.val < 755 then (130, 196) else (131, 151))))))) else (if i.val < 774 then (if i.val < 765 then (if i.val < 760 then (if i.val < 758 then (if i.val < 757 then (144, 44) else (61, 202)) else (if i.val < 759 then (139, 212) else (75, 240))) else (if i.val < 762 then (if i.val < 761 then (114, 0) else (84, 32)) else (if i.val < 763 then (143, 242) else (if i.val < 764 then (38, 131) else (104, 254))))) else (if i.val < 769 then (if i.val < 767 then (if i.val < 766 then (74, 61) else (78, 252)) else (if i.val < 768 then (4, 17) else (58, 129))) else (if i.val < 771 then (if i.val < 770 then (122, 199) else (73, 209)) else (if i.val < 772 then (44, 166) else (if i.val < 773 then (20, 183) else (84, 176)))))) else (if i.val < 783 then (if i.val < 778 then (if i.val < 776 then (if i.val < 775 then (3, 181) else (60, 180)) else (if i.val < 777 then (105, 42) else (85, 191))) else (if i.val < 780 then (if i.val < 779 then (56, 252) else (133, 195)) else (if i.val < 781 then (90, 101) else (if i.val < 782 then (18, 250) else (58, 99))))) else (if i.val < 787 then (if i.val < 785 then (if i.val < 784 then (123, 113) else (133, 246)) else (if i.val < 786 then (68, 56) else (110, 218))) else (if i.val < 789 then (if i.val < 788 then (25, 32) else (78, 166)) else (if i.val < 790 then (62, 171) else (if i.val < 791 then (31, 94) else (110, 115)))))))) else (if i.val < 828 then (if i.val < 810 then (if i.val < 801 then (if i.val < 796 then (if i.val < 794 then (if i.val < 793 then (61, 4) else (50, 159)) else (if i.val < 795 then (3, 219) else (20, 222))) else (if i.val < 798 then (if i.val < 797 then (61, 88) else (4, 219)) else (if i.val < 799 then (28, 10) else (if i.val < 800 then (126, 35) else (90, 253))))) else (if i.val < 805 then (if i.val < 803 then (if i.val < 802 then (36, 176) else (88, 54)) else (if i.val < 804 then (38, 115) else (9, 178))) else (if i.val < 807 then (if i.val < 806 then (102, 161) else (79, 170)) else (if i.val < 808 then (104, 110) else (if i.val < 809 then (60, 200) else (125, 129)))))) else (if i.val < 819 then (if i.val < 814 then (if i.val < 812 then (if i.val < 811 then (126, 70) else (28, 26)) else (if i.val < 813 then (28, 111) else (144, 50))) else (if i.val < 816 then (if i.val < 815 then (67, 165) else (117, 205)) else (if i.val < 817 then (39, 152) else (if i.val < 818 then (142, 23) else (78, 241))))) else (if i.val < 823 then (if i.val < 821 then (if i.val < 820 then (135, 97) else (135, 203)) else (if i.val < 822 then (130, 98) else (134, 49))) else (if i.val < 825 then (if i.val < 824 then (42, 149) else (136, 58)) else (if i.val < 826 then (83, 132) else (if i.val < 827 then (78, 178) else (57, 134))))))) else (if i.val < 846 then (if i.val < 837 then (if i.val < 832 then (if i.val < 830 then (if i.val < 829 then (129, 183) else (142, 211)) else (if i.val < 831 then (8, 161) else (63, 112))) else (if i.val < 834 then (if i.val < 833 then (76, 20) else (132, 79)) else (if i.val < 835 then (53, 68) else (if i.val < 836 then (57, 243) else (68, 39))))) else (if i.val < 841 then (if i.val < 839 then (if i.val < 838 then (108, 56) else (86, 200)) else (if i.val < 840 then (92, 118) else (52, 154))) else (if i.val < 843 then (if i.val < 842 then (81, 190) else (120, 7)) else (if i.val < 844 then (82, 233) else (if i.val < 845 then (93, 135) else (144, 91)))))) else (if i.val < 855 then (if i.val < 850 then (if i.val < 848 then (if i.val < 847 then (53, 197) else (86, 76)) else (if i.val < 849 then (54, 23) else (4, 67))) else (if i.val < 852 then (if i.val < 851 then (65, 183) else (92, 58)) else (if i.val < 853 then (120, 182) else (if i.val < 854 then (43, 68) else (58, 52))))) else (if i.val < 859 then (if i.val < 857 then (if i.val < 856 then (95, 114) else (92, 234)) else (if i.val < 858 then (53, 118) else (144, 128))) else (if i.val < 861 then (if i.val < 860 then (68, 42) else (81, 86)) else (if i.val < 862 then (81, 247) else (if i.val < 863 then (117, 179) else (93, 153)))))))))) else (if i.val < 1008 then (if i.val < 936 then (if i.val < 900 then (if i.val < 882 then (if i.val < 873 then (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then (135, 151) else (129, 22)) else (if i.val < 867 then (109, 49) else (0, 34))) else (if i.val < 870 then (if i.val < 869 then (14, 93) else (11, 2)) else (if i.val < 871 then (132, 44) else (if i.val < 872 then (67, 33) else (54, 79))))) else (if i.val < 877 then (if i.val < 875 then (if i.val < 874 then (94, 42) else (129, 13)) else (if i.val < 876 then (78, 161) else (127, 115))) else (if i.val < 879 then (if i.val < 878 then (130, 31) else (112, 204)) else (if i.val < 880 then (112, 164) else (if i.val < 881 then (81, 188) else (129, 232)))))) else (if i.val < 891 then (if i.val < 886 then (if i.val < 884 then (if i.val < 883 then (53, 198) else (141, 87)) else (if i.val < 885 then (142, 22) else (64, 184))) else (if i.val < 888 then (if i.val < 887 then (129, 61) else (141, 11)) else (if i.val < 889 then (39, 42) else (if i.val < 890 then (94, 219) else (106, 3))))) else (if i.val < 895 then (if i.val < 893 then (if i.val < 892 then (83, 89) else (119, 202)) else (if i.val < 894 then (83, 85) else (13, 208))) else (if i.val < 897 then (if i.val < 896 then (119, 133) else (5, 71)) else (if i.val < 898 then (141, 56) else (if i.val < 899 then (140, 132) else (94, 185))))))) else (if i.val < 918 then (if i.val < 909 then (if i.val < 904 then (if i.val < 902 then (if i.val < 901 then (140, 170) else (142, 255)) else (if i.val < 903 then (108, 48) else (144, 101))) else (if i.val < 906 then (if i.val < 905 then (135, 84) else (68, 20)) else (if i.val < 907 then (60, 77) else (if i.val < 908 then (28, 77) else (28, 13))))) else (if i.val < 913 then (if i.val < 911 then (if i.val < 910 then (62, 69) else (67, 9)) else (if i.val < 912 then (140, 11) else (134, 168))) else (if i.val < 915 then (if i.val < 914 then (81, 198) else (108, 129)) else (if i.val < 916 then (9, 248) else (if i.val < 917 then (109, 104) else (29, 49)))))) else (if i.val < 927 then (if i.val < 922 then (if i.val < 920 then (if i.val < 919 then (50, 127) else (83, 77)) else (if i.val < 921 then (81, 228) else (113, 172))) else (if i.val < 924 then (if i.val < 923 then (143, 48) else (88, 72)) else (if i.val < 925 then (144, 132) else (if i.val < 926 then (80, 196) else (52, 253))))) else (if i.val < 931 then (if i.val < 929 then (if i.val < 928 then (142, 245) else (57, 148)) else (if i.val < 930 then (134, 173) else (19, 230))) else (if i.val < 933 then (if i.val < 932 then (32, 234) else (35, 16)) else (if i.val < 934 then (40, 125) else (if i.val < 935 then (123, 177) else (99, 4)))))))) else (if i.val < 972 then (if i.val < 954 then (if i.val < 945 then (if i.val < 940 then (if i.val < 938 then (if i.val < 937 then (136, 174) else (58, 100)) else (if i.val < 939 then (117, 114) else (74, 137))) else (if i.val < 942 then (if i.val < 941 then (44, 61) else (118, 85)) else (if i.val < 943 then (118, 250) else (if i.val < 944 then (11, 16) else (118, 181))))) else (if i.val < 949 then (if i.val < 947 then (if i.val < 946 then (10, 137) else (117, 47)) else (if i.val < 948 then (10, 62) else (58, 93))) else (if i.val < 951 then (if i.val < 950 then (97, 12) else (112, 12)) else (if i.val < 952 then (98, 157) else (if i.val < 953 then (7, 208) else (75, 123)))))) else (if i.val < 963 then (if i.val < 958 then (if i.val < 956 then (if i.val < 955 then (138, 93) else (131, 82)) else (if i.val < 957 then (131, 17) else (121, 89))) else (if i.val < 960 then (if i.val < 959 then (138, 109) else (34, 248)) else (if i.val < 961 then (108, 69) else (if i.val < 962 then (124, 130) else (69, 28))))) else (if i.val < 967 then (if i.val < 965 then (if i.val < 964 then (81, 48) else (132, 81)) else (if i.val < 966 then (109, 254) else (136, 25))) else (if i.val < 969 then (if i.val < 968 then (92, 36) else (43, 34)) else (if i.val < 970 then (42, 210) else (if i.val < 971 then (83, 54) else (40, 158))))))) else (if i.val < 990 then (if i.val < 981 then (if i.val < 976 then (if i.val < 974 then (if i.val < 973 then (117, 173) else (66, 85)) else (if i.val < 975 then (128, 208) else (29, 41))) else (if i.val < 978 then (if i.val < 977 then (136, 145) else (93, 57)) else (if i.val < 979 then (65, 67) else (if i.val < 980 then (73, 24) else (131, 13))))) else (if i.val < 985 then (if i.val < 983 then (if i.val < 982 then (32, 235) else (112, 199)) else (if i.val < 984 then (122, 54) else (87, 145))) else (if i.val < 987 then (if i.val < 986 then (25, 30) else (87, 27)) else (if i.val < 988 then (138, 161) else (if i.val < 989 then (86, 143) else (117, 175)))))) else (if i.val < 999 then (if i.val < 994 then (if i.val < 992 then (if i.val < 991 then (142, 65) else (98, 70)) else (if i.val < 993 then (136, 81) else (138, 61))) else (if i.val < 996 then (if i.val < 995 then (79, 188) else (54, 35)) else (if i.val < 997 then (143, 55) else (if i.val < 998 then (82, 41) else (55, 14))))) else (if i.val < 1003 then (if i.val < 1001 then (if i.val < 1000 then (74, 26) else (33, 53)) else (if i.val < 1002 then (143, 49) else (62, 43))) else (if i.val < 1005 then (if i.val < 1004 then (116, 2) else (88, 69)) else (if i.val < 1006 then (55, 54) else (if i.val < 1007 then (46, 121) else (33, 49))))))))) else (if i.val < 1080 then (if i.val < 1044 then (if i.val < 1026 then (if i.val < 1017 then (if i.val < 1012 then (if i.val < 1010 then (if i.val < 1009 then (111, 129) else (64, 193)) else (if i.val < 1011 then (37, 60) else (90, 63))) else (if i.val < 1014 then (if i.val < 1013 then (87, 55) else (124, 101)) else (if i.val < 1015 then (37, 110) else (if i.val < 1016 then (123, 165) else (34, 52))))) else (if i.val < 1021 then (if i.val < 1019 then (if i.val < 1018 then (60, 227) else (51, 202)) else (if i.val < 1020 then (97, 248) else (70, 162))) else (if i.val < 1023 then (if i.val < 1022 then (72, 34) else (137, 189)) else (if i.val < 1024 then (47, 220) else (if i.val < 1025 then (7, 205) else (81, 152)))))) else (if i.val < 1035 then (if i.val < 1030 then (if i.val < 1028 then (if i.val < 1027 then (131, 61) else (84, 25)) else (if i.val < 1029 then (138, 181) else (138, 156))) else (if i.val < 1032 then (if i.val < 1031 then (102, 35) else (72, 195)) else (if i.val < 1033 then (47, 64) else (if i.val < 1034 then (122, 224) else (88, 150))))) else (if i.val < 1039 then (if i.val < 1037 then (if i.val < 1036 then (134, 75) else (113, 194)) else (if i.val < 1038 then (59, 187) else (140, 109))) else (if i.val < 1041 then (if i.val < 1040 then (10, 43) else (15, 227)) else (if i.val < 1042 then (124, 48) else (if i.val < 1043 then (66, 75) else (124, 127))))))) else (if i.val < 1062 then (if i.val < 1053 then (if i.val < 1048 then (if i.val < 1046 then (if i.val < 1045 then (102, 33) else (98, 68)) else (if i.val < 1047 then (107, 198) else (86, 247))) else (if i.val < 1050 then (if i.val < 1049 then (120, 236) else (70, 164)) else (if i.val < 1051 then (70, 81) else (if i.val < 1052 then (43, 93) else (25, 115))))) else (if i.val < 1057 then (if i.val < 1055 then (if i.val < 1054 then (135, 19) else (11, 242)) else (if i.val < 1056 then (128, 86) else (85, 145))) else (if i.val < 1059 then (if i.val < 1058 then (137, 57) else (46, 253)) else (if i.val < 1060 then (74, 151) else (if i.val < 1061 then (80, 54) else (106, 197)))))) else (if i.val < 1071 then (if i.val < 1066 then (if i.val < 1064 then (if i.val < 1063 then (117, 93) else (108, 119)) else (if i.val < 1065 then (92, 80) else (54, 239))) else (if i.val < 1068 then (if i.val < 1067 then (41, 212) else (33, 106)) else (if i.val < 1069 then (91, 98) else (if i.val < 1070 then (116, 142) else (28, 136))))) else (if i.val < 1075 then (if i.val < 1073 then (if i.val < 1072 then (115, 219) else (80, 136)) else (if i.val < 1074 then (62, 109) else (91, 186))) else (if i.val < 1077 then (if i.val < 1076 then (36, 212) else (133, 172)) else (if i.val < 1078 then (85, 197) else (if i.val < 1079 then (91, 14) else (51, 98)))))))) else (if i.val < 1116 then (if i.val < 1098 then (if i.val < 1089 then (if i.val < 1084 then (if i.val < 1082 then (if i.val < 1081 then (90, 118) else (38, 216)) else (if i.val < 1083 then (89, 41) else (134, 88))) else (if i.val < 1086 then (if i.val < 1085 then (76, 152) else (37, 188)) else (if i.val < 1087 then (38, 42) else (if i.val < 1088 then (79, 181) else (127, 87))))) else (if i.val < 1093 then (if i.val < 1091 then (if i.val < 1090 then (103, 57) else (80, 76)) else (if i.val < 1092 then (18, 200) else (77, 194))) else (if i.val < 1095 then (if i.val < 1094 then (19, 121) else (75, 227)) else (if i.val < 1096 then (56, 247) else (if i.val < 1097 then (138, 219) else (129, 14)))))) else (if i.val < 1107 then (if i.val < 1102 then (if i.val < 1100 then (if i.val < 1099 then (38, 171) else (62, 19)) else (if i.val < 1101 then (39, 93) else (135, 79))) else (if i.val < 1104 then (if i.val < 1103 then (82, 26) else (116, 87)) else (if i.val < 1105 then (33, 47) else (if i.val < 1106 then (129, 16) else (64, 126))))) else (if i.val < 1111 then (if i.val < 1109 then (if i.val < 1108 then (53, 160) else (39, 172)) else (if i.val < 1110 then (42, 144) else (135, 6))) else (if i.val < 1113 then (if i.val < 1112 then (41, 25) else (129, 196)) else (if i.val < 1114 then (136, 96) else (if i.val < 1115 then (41, 7) else (23, 59))))))) else (if i.val < 1134 then (if i.val < 1125 then (if i.val < 1120 then (if i.val < 1118 then (if i.val < 1117 then (90, 128) else (110, 13)) else (if i.val < 1119 then (141, 39) else (135, 107))) else (if i.val < 1122 then (if i.val < 1121 then (66, 50) else (129, 98)) else (if i.val < 1123 then (135, 150) else (if i.val < 1124 then (21, 60) else (23, 63))))) else (if i.val < 1129 then (if i.val < 1127 then (if i.val < 1126 then (66, 240) else (131, 195)) else (if i.val < 1128 then (82, 152) else (86, 139))) else (if i.val < 1131 then (if i.val < 1130 then (140, 127) else (10, 91)) else (if i.val < 1132 then (83, 74) else (if i.val < 1133 then (43, 61) else (136, 86)))))) else (if i.val < 1143 then (if i.val < 1138 then (if i.val < 1136 then (if i.val < 1135 then (95, 214) else (43, 74)) else (if i.val < 1137 then (23, 157) else (14, 94))) else (if i.val < 1140 then (if i.val < 1139 then (22, 54) else (42, 227)) else (if i.val < 1141 then (107, 194) else (if i.val < 1142 then (67, 172) else (5, 116))))) else (if i.val < 1147 then (if i.val < 1145 then (if i.val < 1144 then (21, 158) else (95, 170)) else (if i.val < 1146 then (94, 67) else (18, 198))) else (if i.val < 1149 then (if i.val < 1148 then (32, 243) else (17, 251)) else (if i.val < 1150 then (41, 27) else (if i.val < 1151 then (63, 174) else (102, 216))))))))))))

def g32p_supplierGroup19_classify : Fin 1152 → Fin 102 :=
  fun i => (if i.val < 576 then (if i.val < 288 then (if i.val < 144 then (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 34) else (if i.val < 3 then 69 else 6)) else (if i.val < 6 then (if i.val < 5 then 18 else 97) else (if i.val < 7 then 90 else (if i.val < 8 then 35 else 57)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 90 else 99) else (if i.val < 12 then 75 else 38)) else (if i.val < 15 then (if i.val < 14 then 35 else 75) else (if i.val < 16 then 6 else (if i.val < 17 then 18 else 57))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then 38 else 18) else (if i.val < 21 then 69 else 13)) else (if i.val < 24 then (if i.val < 23 then 84 else 82) else (if i.val < 25 then 13 else (if i.val < 26 then 34 else 15)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then 57 else 84) else (if i.val < 30 then 35 else 32)) else (if i.val < 33 then (if i.val < 32 then 57 else 82) else (if i.val < 34 then 57 else (if i.val < 35 then 65 else 34)))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then 35 else 57) else (if i.val < 39 then 69 else 75)) else (if i.val < 42 then (if i.val < 41 then 18 else 15) else (if i.val < 43 then 75 else (if i.val < 44 then 6 else 18)))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then 57 else 18) else (if i.val < 48 then 38 else 15)) else (if i.val < 51 then (if i.val < 50 then 32 else 65) else (if i.val < 52 then 35 else (if i.val < 53 then 6 else 38))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then 32 else 6) else (if i.val < 57 then 57 else 18)) else (if i.val < 60 then (if i.val < 59 then 57 else 57) else (if i.val < 61 then 34 else (if i.val < 62 then 57 else 18)))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then 69 else 65) else (if i.val < 66 then 38 else 101)) else (if i.val < 69 then (if i.val < 68 then 94 else 75) else (if i.val < 70 then 38 else (if i.val < 71 then 94 else 96))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 45 else 49) else (if i.val < 75 then 75 else 45)) else (if i.val < 78 then (if i.val < 77 then 84 else 82) else (if i.val < 79 then 38 else (if i.val < 80 then 49 else 82)))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then 82 else 86) else (if i.val < 84 then 49 else 31)) else (if i.val < 87 then (if i.val < 86 then 32 else 57) else (if i.val < 88 then 45 else (if i.val < 89 then 66 else 35))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then 57 else 49) else (if i.val < 93 then 57 else 57)) else (if i.val < 96 then (if i.val < 95 then 86 else 45) else (if i.val < 97 then 49 else (if i.val < 98 then 45 else 15)))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then 57 else 84) else (if i.val < 102 then 66 else 82)) else (if i.val < 105 then (if i.val < 104 then 57 else 49) else (if i.val < 106 then 49 else (if i.val < 107 then 13 else 49)))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 34 else 34) else (if i.val < 111 then 82 else 57)) else (if i.val < 114 then (if i.val < 113 then 31 else 66) else (if i.val < 115 then 57 else (if i.val < 116 then 86 else 32)))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 66 else 57) else (if i.val < 120 then 49 else 57)) else (if i.val < 123 then (if i.val < 122 then 57 else 6) else (if i.val < 124 then 38 else (if i.val < 125 then 32 else 6))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then 75 else 18) else (if i.val < 129 then 57 else 38)) else (if i.val < 132 then (if i.val < 131 then 18 else 32) else (if i.val < 133 then 15 else (if i.val < 134 then 34 else 66)))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then 38 else 35) else (if i.val < 138 then 75 else 57)) else (if i.val < 141 then (if i.val < 140 then 57 else 57) else (if i.val < 142 then 34 else (if i.val < 143 then 57 else 38)))))))) else (if i.val < 216 then (if i.val < 180 then (if i.val < 162 then (if i.val < 153 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 69 else 57) else (if i.val < 147 then 86 else 35)) else (if i.val < 150 then (if i.val < 149 then 57 else 45) else (if i.val < 151 then 15 else (if i.val < 152 then 34 else 57)))) else (if i.val < 157 then (if i.val < 155 then (if i.val < 154 then 49 else 66) else (if i.val < 156 then 66 else 57)) else (if i.val < 159 then (if i.val < 158 then 15 else 57) else (if i.val < 160 then 35 else (if i.val < 161 then 34 else 57))))) else (if i.val < 171 then (if i.val < 166 then (if i.val < 164 then (if i.val < 163 then 66 else 69) else (if i.val < 165 then 18 else 57)) else (if i.val < 168 then (if i.val < 167 then 65 else 32) else (if i.val < 169 then 57 else (if i.val < 170 then 49 else 57)))) else (if i.val < 175 then (if i.val < 173 then (if i.val < 172 then 90 else 57) else (if i.val < 174 then 65 else 35)) else (if i.val < 177 then (if i.val < 176 then 13 else 34) else (if i.val < 178 then 57 else (if i.val < 179 then 57 else 90)))))) else (if i.val < 198 then (if i.val < 189 then (if i.val < 184 then (if i.val < 182 then (if i.val < 181 then 38 else 38) else (if i.val < 183 then 75 else 34)) else (if i.val < 186 then (if i.val < 185 then 69 else 6) else (if i.val < 187 then 57 else (if i.val < 188 then 57 else 35)))) else (if i.val < 193 then (if i.val < 191 then (if i.val < 190 then 57 else 38) else (if i.val < 192 then 13 else 34)) else (if i.val < 195 then (if i.val < 194 then 35 else 65) else (if i.val < 196 then 34 else (if i.val < 197 then 69 else 71))))) else (if i.val < 207 then (if i.val < 202 then (if i.val < 200 then (if i.val < 199 then 38 else 35) else (if i.val < 201 then 75 else 6)) else (if i.val < 204 then (if i.val < 203 then 38 else 38) else (if i.val < 205 then 18 else (if i.val < 206 then 69 else 75)))) else (if i.val < 211 then (if i.val < 209 then (if i.val < 208 then 38 else 13) else (if i.val < 210 then 45 else 82)) else (if i.val < 213 then (if i.val < 212 then 71 else 45) else (if i.val < 214 then 84 else (if i.val < 215 then 82 else 38))))))) else (if i.val < 252 then (if i.val < 234 then (if i.val < 225 then (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 82 else 49) else (if i.val < 219 then 71 else 6)) else (if i.val < 222 then (if i.val < 221 then 18 else 75) else (if i.val < 223 then 84 else (if i.val < 224 then 49 else 6)))) else (if i.val < 229 then (if i.val < 227 then (if i.val < 226 then 84 else 38) else (if i.val < 228 then 82 else 38)) else (if i.val < 231 then (if i.val < 230 then 38 else 69) else (if i.val < 232 then 38 else (if i.val < 233 then 82 else 13))))) else (if i.val < 243 then (if i.val < 238 then (if i.val < 236 then (if i.val < 235 then 18 else 49) else (if i.val < 237 then 13 else 86)) else (if i.val < 240 then (if i.val < 239 then 13 else 75) else (if i.val < 241 then 86 else (if i.val < 242 then 86 else 13)))) else (if i.val < 247 then (if i.val < 245 then (if i.val < 244 then 38 else 13) else (if i.val < 246 then 49 else 66)) else (if i.val < 249 then (if i.val < 248 then 57 else 45) else (if i.val < 250 then 32 else (if i.val < 251 then 82 else 57)))))) else (if i.val < 270 then (if i.val < 261 then (if i.val < 256 then (if i.val < 254 then (if i.val < 253 then 86 else 86) else (if i.val < 255 then 49 else 45)) else (if i.val < 258 then (if i.val < 257 then 57 else 84) else (if i.val < 259 then 66 else (if i.val < 260 then 82 else 13)))) else (if i.val < 265 then (if i.val < 263 then (if i.val < 262 then 49 else 83) else (if i.val < 264 then 82 else 90)) else (if i.val < 267 then (if i.val < 266 then 49 else 71) else (if i.val < 268 then 86 else (if i.val < 269 then 49 else 84))))) else (if i.val < 279 then (if i.val < 274 then (if i.val < 272 then (if i.val < 271 then 49 else 86) else (if i.val < 273 then 84 else 49)) else (if i.val < 276 then (if i.val < 275 then 84 else 49) else (if i.val < 277 then 86 else (if i.val < 278 then 13 else 49)))) else (if i.val < 283 then (if i.val < 281 then (if i.val < 280 then 84 else 34) else (if i.val < 282 then 13 else 49)) else (if i.val < 285 then (if i.val < 284 then 84 else 82) else (if i.val < 286 then 38 else (if i.val < 287 then 49 else 83))))))))) else (if i.val < 432 then (if i.val < 360 then (if i.val < 324 then (if i.val < 306 then (if i.val < 297 then (if i.val < 292 then (if i.val < 290 then (if i.val < 289 then 49 else 49) else (if i.val < 291 then 84 else 69)) else (if i.val < 294 then (if i.val < 293 then 52 else 13) else (if i.val < 295 then 49 else (if i.val < 296 then 52 else 57)))) else (if i.val < 301 then (if i.val < 299 then (if i.val < 298 then 57 else 15) else (if i.val < 300 then 13 else 31)) else (if i.val < 303 then (if i.val < 302 then 15 else 49) else (if i.val < 304 then 82 else (if i.val < 305 then 45 else 49))))) else (if i.val < 315 then (if i.val < 310 then (if i.val < 308 then (if i.val < 307 then 57 else 34) else (if i.val < 309 then 32 else 57)) else (if i.val < 312 then (if i.val < 311 then 66 else 66) else (if i.val < 313 then 57 else (if i.val < 314 then 13 else 57)))) else (if i.val < 319 then (if i.val < 317 then (if i.val < 316 then 34 else 84) else (if i.val < 318 then 49 else 35)) else (if i.val < 321 then (if i.val < 320 then 57 else 86) else (if i.val < 322 then 35 else (if i.val < 323 then 57 else 82)))))) else (if i.val < 342 then (if i.val < 333 then (if i.val < 328 then (if i.val < 326 then (if i.val < 325 then 49 else 52) else (if i.val < 327 then 13 else 57)) else (if i.val < 330 then (if i.val < 329 then 31 else 49) else (if i.val < 331 then 65 else (if i.val < 332 then 66 else 75)))) else (if i.val < 337 then (if i.val < 335 then (if i.val < 334 then 57 else 18) else (if i.val < 336 then 66 else 32)) else (if i.val < 339 then (if i.val < 338 then 35 else 57) else (if i.val < 340 then 57 else (if i.val < 341 then 57 else 66))))) else (if i.val < 351 then (if i.val < 346 then (if i.val < 344 then (if i.val < 343 then 57 else 86) else (if i.val < 345 then 57 else 49)) else (if i.val < 348 then (if i.val < 347 then 32 else 35) else (if i.val < 349 then 57 else (if i.val < 350 then 57 else 35)))) else (if i.val < 355 then (if i.val < 353 then (if i.val < 352 then 90 else 57) else (if i.val < 354 then 66 else 57)) else (if i.val < 357 then (if i.val < 356 then 57 else 15) else (if i.val < 358 then 13 else (if i.val < 359 then 90 else 57))))))) else (if i.val < 396 then (if i.val < 378 then (if i.val < 369 then (if i.val < 364 then (if i.val < 362 then (if i.val < 361 then 34 else 66) else (if i.val < 363 then 83 else 57)) else (if i.val < 366 then (if i.val < 365 then 57 else 31) else (if i.val < 367 then 90 else (if i.val < 368 then 65 else 57)))) else (if i.val < 373 then (if i.val < 371 then (if i.val < 370 then 15 else 86) else (if i.val < 372 then 49 else 86)) else (if i.val < 375 then (if i.val < 374 then 49 else 57) else (if i.val < 376 then 86 else (if i.val < 377 then 13 else 82))))) else (if i.val < 387 then (if i.val < 382 then (if i.val < 380 then (if i.val < 379 then 84 else 57) else (if i.val < 381 then 49 else 49)) else (if i.val < 384 then (if i.val < 383 then 45 else 66) else (if i.val < 385 then 34 else (if i.val < 386 then 84 else 35)))) else (if i.val < 391 then (if i.val < 389 then (if i.val < 388 then 90 else 57) else (if i.val < 390 then 49 else 57)) else (if i.val < 393 then (if i.val < 392 then 57 else 66) else (if i.val < 394 then 34 else (if i.val < 395 then 57 else 57)))))) else (if i.val < 414 then (if i.val < 405 then (if i.val < 400 then (if i.val < 398 then (if i.val < 397 then 34 else 66) else (if i.val < 399 then 86 else 90)) else (if i.val < 402 then (if i.val < 401 then 57 else 13) else (if i.val < 403 then 90 else (if i.val < 404 then 65 else 66)))) else (if i.val < 409 then (if i.val < 407 then (if i.val < 406 then 90 else 57) else (if i.val < 408 then 57 else 35)) else (if i.val < 411 then (if i.val < 410 then 57 else 57) else (if i.val < 412 then 34 else (if i.val < 413 then 84 else 15))))) else (if i.val < 423 then (if i.val < 418 then (if i.val < 416 then (if i.val < 415 then 57 else 57) else (if i.val < 417 then 66 else 13)) else (if i.val < 420 then (if i.val < 419 then 13 else 13) else (if i.val < 421 then 49 else (if i.val < 422 then 35 else 49)))) else (if i.val < 427 then (if i.val < 425 then (if i.val < 424 then 49 else 84) else (if i.val < 426 then 57 else 34)) else (if i.val < 429 then (if i.val < 428 then 49 else 57) else (if i.val < 430 then 57 else (if i.val < 431 then 15 else 15)))))))) else (if i.val < 504 then (if i.val < 468 then (if i.val < 450 then (if i.val < 441 then (if i.val < 436 then (if i.val < 434 then (if i.val < 433 then 49 else 82) else (if i.val < 435 then 45 else 57)) else (if i.val < 438 then (if i.val < 437 then 57 else 52) else (if i.val < 439 then 52 else (if i.val < 440 then 37 else 32)))) else (if i.val < 445 then (if i.val < 443 then (if i.val < 442 then 57 else 45) else (if i.val < 444 then 32 else 35)) else (if i.val < 447 then (if i.val < 446 then 65 else 57) else (if i.val < 448 then 65 else (if i.val < 449 then 65 else 66))))) else (if i.val < 459 then (if i.val < 454 then (if i.val < 452 then (if i.val < 451 then 57 else 5) else (if i.val < 453 then 6 else 38)) else (if i.val < 456 then (if i.val < 455 then 32 else 40) else (if i.val < 457 then 75 else (if i.val < 458 then 38 else 38)))) else (if i.val < 463 then (if i.val < 461 then (if i.val < 460 then 38 else 32) else (if i.val < 462 then 71 else 38)) else (if i.val < 465 then (if i.val < 464 then 40 else 38) else (if i.val < 466 then 57 else (if i.val < 467 then 69 else 69)))))) else (if i.val < 486 then (if i.val < 477 then (if i.val < 472 then (if i.val < 470 then (if i.val < 469 then 65 else 38) else (if i.val < 471 then 5 else 40)) else (if i.val < 474 then (if i.val < 473 then 38 else 6) else (if i.val < 475 then 40 else (if i.val < 476 then 38 else 38)))) else (if i.val < 481 then (if i.val < 479 then (if i.val < 478 then 38 else 84) else (if i.val < 480 then 49 else 6)) else (if i.val < 483 then (if i.val < 482 then 84 else 38) else (if i.val < 484 then 49 else (if i.val < 485 then 6 else 71))))) else (if i.val < 495 then (if i.val < 490 then (if i.val < 488 then (if i.val < 487 then 69 else 40) else (if i.val < 489 then 49 else 75)) else (if i.val < 492 then (if i.val < 491 then 45 else 38) else (if i.val < 493 then 38 else (if i.val < 494 then 38 else 69)))) else (if i.val < 499 then (if i.val < 497 then (if i.val < 496 then 38 else 13) else (if i.val < 498 then 38 else 66)) else (if i.val < 501 then (if i.val < 500 then 75 else 38) else (if i.val < 502 then 71 else (if i.val < 503 then 38 else 40))))))) else (if i.val < 540 then (if i.val < 522 then (if i.val < 513 then (if i.val < 508 then (if i.val < 506 then (if i.val < 505 then 40 else 38) else (if i.val < 507 then 71 else 38)) else (if i.val < 510 then (if i.val < 509 then 75 else 69) else (if i.val < 511 then 38 else (if i.val < 512 then 40 else 82)))) else (if i.val < 517 then (if i.val < 515 then (if i.val < 514 then 38 else 18) else (if i.val < 516 then 6 else 38)) else (if i.val < 519 then (if i.val < 518 then 57 else 38) else (if i.val < 520 then 94 else (if i.val < 521 then 38 else 18))))) else (if i.val < 531 then (if i.val < 526 then (if i.val < 524 then (if i.val < 523 then 75 else 69) else (if i.val < 525 then 38 else 38)) else (if i.val < 528 then (if i.val < 527 then 94 else 49) else (if i.val < 529 then 45 else (if i.val < 530 then 69 else 13)))) else (if i.val < 535 then (if i.val < 533 then (if i.val < 532 then 84 else 38) else (if i.val < 534 then 38 else 75)) else (if i.val < 537 then (if i.val < 536 then 38 else 49) else (if i.val < 538 then 82 else (if i.val < 539 then 10 else 49)))))) else (if i.val < 558 then (if i.val < 549 then (if i.val < 544 then (if i.val < 542 then (if i.val < 541 then 10 else 10) else (if i.val < 543 then 13 else 38)) else (if i.val < 546 then (if i.val < 545 then 13 else 6) else (if i.val < 547 then 18 else (if i.val < 548 then 49 else 40)))) else (if i.val < 553 then (if i.val < 551 then (if i.val < 550 then 10 else 13) else (if i.val < 552 then 38 else 38)) else (if i.val < 555 then (if i.val < 554 then 69 else 38) else (if i.val < 556 then 13 else (if i.val < 557 then 38 else 13))))) else (if i.val < 567 then (if i.val < 562 then (if i.val < 560 then (if i.val < 559 then 84 else 32) else (if i.val < 561 then 49 else 57)) else (if i.val < 564 then (if i.val < 563 then 10 else 84) else (if i.val < 565 then 49 else (if i.val < 566 then 49 else 45)))) else (if i.val < 571 then (if i.val < 569 then (if i.val < 568 then 49 else 71) else (if i.val < 570 then 49 else 69)) else (if i.val < 573 then (if i.val < 572 then 10 else 10) else (if i.val < 574 then 49 else (if i.val < 575 then 49 else 10)))))))))) else (if i.val < 864 then (if i.val < 720 then (if i.val < 648 then (if i.val < 612 then (if i.val < 594 then (if i.val < 585 then (if i.val < 580 then (if i.val < 578 then (if i.val < 577 then 13 else 49) else (if i.val < 579 then 45 else 13)) else (if i.val < 582 then (if i.val < 581 then 49 else 84) else (if i.val < 583 then 38 else (if i.val < 584 then 13 else 49)))) else (if i.val < 589 then (if i.val < 587 then (if i.val < 586 then 10 else 69) else (if i.val < 588 then 13 else 13)) else (if i.val < 591 then (if i.val < 590 then 13 else 10) else (if i.val < 592 then 6 else (if i.val < 593 then 38 else 49))))) else (if i.val < 603 then (if i.val < 598 then (if i.val < 596 then (if i.val < 595 then 71 else 49) else (if i.val < 597 then 86 else 49)) else (if i.val < 600 then (if i.val < 599 then 40 else 45) else (if i.val < 601 then 13 else (if i.val < 602 then 49 else 38)))) else (if i.val < 607 then (if i.val < 605 then (if i.val < 604 then 49 else 83) else (if i.val < 606 then 49 else 49)) else (if i.val < 609 then (if i.val < 608 then 49 else 86) else (if i.val < 610 then 75 else (if i.val < 611 then 52 else 49)))))) else (if i.val < 630 then (if i.val < 621 then (if i.val < 616 then (if i.val < 614 then (if i.val < 613 then 69 else 13) else (if i.val < 615 then 49 else 10)) else (if i.val < 618 then (if i.val < 617 then 83 else 49) else (if i.val < 619 then 49 else (if i.val < 620 then 10 else 49)))) else (if i.val < 625 then (if i.val < 623 then (if i.val < 622 then 49 else 10) else (if i.val < 624 then 13 else 49)) else (if i.val < 627 then (if i.val < 626 then 45 else 38) else (if i.val < 628 then 18 else (if i.val < 629 then 69 else 38))))) else (if i.val < 639 then (if i.val < 634 then (if i.val < 632 then (if i.val < 631 then 10 else 38) else (if i.val < 633 then 49 else 13)) else (if i.val < 636 then (if i.val < 635 then 38 else 49) else (if i.val < 637 then 49 else (if i.val < 638 then 45 else 84)))) else (if i.val < 643 then (if i.val < 641 then (if i.val < 640 then 38 else 38) else (if i.val < 642 then 75 else 49)) else (if i.val < 645 then (if i.val < 644 then 49 else 15) else (if i.val < 646 then 57 else (if i.val < 647 then 35 else 49))))))) else (if i.val < 684 then (if i.val < 666 then (if i.val < 657 then (if i.val < 652 then (if i.val < 650 then (if i.val < 649 then 57 else 32) else (if i.val < 651 then 49 else 13)) else (if i.val < 654 then (if i.val < 653 then 34 else 13) else (if i.val < 655 then 49 else (if i.val < 656 then 13 else 49)))) else (if i.val < 661 then (if i.val < 659 then (if i.val < 658 then 38 else 49) else (if i.val < 660 then 13 else 34)) else (if i.val < 663 then (if i.val < 662 then 57 else 32) else (if i.val < 664 then 34 else (if i.val < 665 then 15 else 45))))) else (if i.val < 675 then (if i.val < 670 then (if i.val < 668 then (if i.val < 667 then 57 else 32) else (if i.val < 669 then 57 else 32)) else (if i.val < 672 then (if i.val < 671 then 57 else 15) else (if i.val < 673 then 15 else (if i.val < 674 then 57 else 32)))) else (if i.val < 679 then (if i.val < 677 then (if i.val < 676 then 57 else 49) else (if i.val < 678 then 31 else 57)) else (if i.val < 681 then (if i.val < 680 then 57 else 31) else (if i.val < 682 then 45 else (if i.val < 683 then 49 else 83)))))) else (if i.val < 702 then (if i.val < 693 then (if i.val < 688 then (if i.val < 686 then (if i.val < 685 then 49 else 49) else (if i.val < 687 then 49 else 45)) else (if i.val < 690 then (if i.val < 689 then 65 else 10) else (if i.val < 691 then 15 else (if i.val < 692 then 49 else 57)))) else (if i.val < 697 then (if i.val < 695 then (if i.val < 694 then 32 else 34) else (if i.val < 696 then 57 else 34)) else (if i.val < 699 then (if i.val < 698 then 15 else 34) else (if i.val < 700 then 57 else (if i.val < 701 then 34 else 15))))) else (if i.val < 711 then (if i.val < 706 then (if i.val < 704 then (if i.val < 703 then 65 else 57) else (if i.val < 705 then 31 else 84)) else (if i.val < 708 then (if i.val < 707 then 35 else 49) else (if i.val < 709 then 10 else (if i.val < 710 then 57 else 34)))) else (if i.val < 715 then (if i.val < 713 then (if i.val < 712 then 13 else 10) else (if i.val < 714 then 6 else 38)) else (if i.val < 717 then (if i.val < 716 then 45 else 52) else (if i.val < 718 then 49 else (if i.val < 719 then 49 else 84)))))))) else (if i.val < 792 then (if i.val < 756 then (if i.val < 738 then (if i.val < 729 then (if i.val < 724 then (if i.val < 722 then (if i.val < 721 then 49 else 6) else (if i.val < 723 then 13 else 13)) else (if i.val < 726 then (if i.val < 725 then 83 else 49) else (if i.val < 727 then 86 else (if i.val < 728 then 13 else 82)))) else (if i.val < 733 then (if i.val < 731 then (if i.val < 730 then 18 else 49) else (if i.val < 732 then 10 else 49)) else (if i.val < 735 then (if i.val < 734 then 82 else 75) else (if i.val < 736 then 45 else (if i.val < 737 then 49 else 83))))) else (if i.val < 747 then (if i.val < 742 then (if i.val < 740 then (if i.val < 739 then 49 else 57) else (if i.val < 741 then 49 else 10)) else (if i.val < 744 then (if i.val < 743 then 49 else 82) else (if i.val < 745 then 57 else (if i.val < 746 then 31 else 57)))) else (if i.val < 751 then (if i.val < 749 then (if i.val < 748 then 83 else 34) else (if i.val < 750 then 49 else 49)) else (if i.val < 753 then (if i.val < 752 then 15 else 57) else (if i.val < 754 then 86 else (if i.val < 755 then 49 else 57)))))) else (if i.val < 774 then (if i.val < 765 then (if i.val < 760 then (if i.val < 758 then (if i.val < 757 then 57 else 34) else (if i.val < 759 then 57 else 57)) else (if i.val < 762 then (if i.val < 761 then 49 else 49) else (if i.val < 763 then 49 else (if i.val < 764 then 34 else 66)))) else (if i.val < 769 then (if i.val < 767 then (if i.val < 766 then 49 else 65) else (if i.val < 768 then 69 else 10)) else (if i.val < 771 then (if i.val < 770 then 49 else 45) else (if i.val < 772 then 49 else (if i.val < 773 then 34 else 86))))) else (if i.val < 783 then (if i.val < 778 then (if i.val < 776 then (if i.val < 775 then 65 else 32) else (if i.val < 777 then 57 else 15)) else (if i.val < 780 then (if i.val < 779 then 31 else 57) else (if i.val < 781 then 35 else (if i.val < 782 then 32 else 10)))) else (if i.val < 787 then (if i.val < 785 then (if i.val < 784 then 49 else 57) else (if i.val < 786 then 69 else 86)) else (if i.val < 789 then (if i.val < 788 then 13 else 34) else (if i.val < 790 then 32 else (if i.val < 791 then 65 else 86))))))) else (if i.val < 828 then (if i.val < 810 then (if i.val < 801 then (if i.val < 796 then (if i.val < 794 then (if i.val < 793 then 32 else 35) else (if i.val < 795 then 65 else 65)) else (if i.val < 798 then (if i.val < 797 then 57 else 45) else (if i.val < 799 then 35 else (if i.val < 800 then 57 else 35)))) else (if i.val < 805 then (if i.val < 803 then (if i.val < 802 then 65 else 49) else (if i.val < 804 then 65 else 34)) else (if i.val < 807 then (if i.val < 806 then 57 else 34) else (if i.val < 808 then 66 else (if i.val < 809 then 34 else 66))))) else (if i.val < 819 then (if i.val < 814 then (if i.val < 812 then (if i.val < 811 then 66 else 34) else (if i.val < 813 then 34 else 57)) else (if i.val < 816 then (if i.val < 815 then 40 else 38) else (if i.val < 817 then 6 else (if i.val < 818 then 38 else 66)))) else (if i.val < 823 then (if i.val < 821 then (if i.val < 820 then 38 else 40) else (if i.val < 822 then 94 else 57)) else (if i.val < 825 then (if i.val < 824 then 69 else 38) else (if i.val < 826 then 71 else (if i.val < 827 then 34 else 5)))))) else (if i.val < 846 then (if i.val < 837 then (if i.val < 832 then (if i.val < 830 then (if i.val < 829 then 71 else 57) else (if i.val < 831 then 65 else 32)) else (if i.val < 834 then (if i.val < 833 then 57 else 38) else (if i.val < 835 then 69 else (if i.val < 836 then 6 else 38)))) else (if i.val < 841 then (if i.val < 839 then (if i.val < 838 then 40 else 40) else (if i.val < 840 then 38 else 69)) else (if i.val < 843 then (if i.val < 842 then 38 else 75) else (if i.val < 844 then 38 else (if i.val < 845 then 5 else 57))))) else (if i.val < 855 then (if i.val < 850 then (if i.val < 848 then (if i.val < 847 then 18 else 40) else (if i.val < 849 then 38 else 40)) else (if i.val < 852 then (if i.val < 851 then 6 else 38) else (if i.val < 853 then 38 else (if i.val < 854 then 40 else 38)))) else (if i.val < 859 then (if i.val < 857 then (if i.val < 856 then 38 else 6) else (if i.val < 858 then 75 else 38)) else (if i.val < 861 then (if i.val < 860 then 38 else 75) else (if i.val < 862 then 94 else (if i.val < 863 then 38 else 40))))))))) else (if i.val < 1008 then (if i.val < 936 then (if i.val < 900 then (if i.val < 882 then (if i.val < 873 then (if i.val < 868 then (if i.val < 866 then (if i.val < 865 then 38 else 38) else (if i.val < 867 then 71 else 34)) else (if i.val < 870 then (if i.val < 869 then 94 else 69) else (if i.val < 871 then 40 else (if i.val < 872 then 5 else 94)))) else (if i.val < 877 then (if i.val < 875 then (if i.val < 874 then 38 else 71) else (if i.val < 876 then 66 else 57)) else (if i.val < 879 then (if i.val < 878 then 38 else 38) else (if i.val < 880 then 40 else (if i.val < 881 then 69 else 75))))) else (if i.val < 891 then (if i.val < 886 then (if i.val < 884 then (if i.val < 883 then 94 else 38) else (if i.val < 885 then 38 else 69)) else (if i.val < 888 then (if i.val < 887 then 38 else 38) else (if i.val < 889 then 69 else (if i.val < 890 then 40 else 66)))) else (if i.val < 895 then (if i.val < 893 then (if i.val < 892 then 94 else 38) else (if i.val < 894 then 94 else 18)) else (if i.val < 897 then (if i.val < 896 then 40 else 94) else (if i.val < 898 then 38 else (if i.val < 899 then 38 else 75)))))) else (if i.val < 918 then (if i.val < 909 then (if i.val < 904 then (if i.val < 902 then (if i.val < 901 then 38 else 38) else (if i.val < 903 then 71 else 38)) else (if i.val < 906 then (if i.val < 905 then 38 else 40) else (if i.val < 907 then 34 else (if i.val < 908 then 34 else 34)))) else (if i.val < 913 then (if i.val < 911 then (if i.val < 910 then 57 else 75) else (if i.val < 912 then 57 else 38)) else (if i.val < 915 then (if i.val < 914 then 69 else 38) else (if i.val < 916 then 38 else (if i.val < 917 then 71 else 71))))) else (if i.val < 927 then (if i.val < 922 then (if i.val < 920 then (if i.val < 919 then 57 else 38) else (if i.val < 921 then 38 else 10)) else (if i.val < 924 then (if i.val < 923 then 38 else 10) else (if i.val < 925 then 38 else (if i.val < 926 then 69 else 69)))) else (if i.val < 931 then (if i.val < 929 then (if i.val < 928 then 38 else 5) else (if i.val < 930 then 38 else 65)) else (if i.val < 933 then (if i.val < 932 then 5 else 13) else (if i.val < 934 then 6 else (if i.val < 935 then 45 else 10))))))) else (if i.val < 972 then (if i.val < 954 then (if i.val < 945 then (if i.val < 940 then (if i.val < 938 then (if i.val < 937 then 49 else 10) else (if i.val < 939 then 38 else 52)) else (if i.val < 942 then (if i.val < 941 then 83 else 40) else (if i.val < 943 then 38 else (if i.val < 944 then 69 else 38)))) else (if i.val < 949 then (if i.val < 947 then (if i.val < 946 then 69 else 38) else (if i.val < 948 then 40 else 10)) else (if i.val < 951 then (if i.val < 950 then 49 else 10) else (if i.val < 952 then 52 else (if i.val < 953 then 13 else 52))))) else (if i.val < 963 then (if i.val < 958 then (if i.val < 956 then (if i.val < 955 then 49 else 49) else (if i.val < 957 then 86 else 49)) else (if i.val < 960 then (if i.val < 959 then 49 else 13) else (if i.val < 961 then 71 else (if i.val < 962 then 86 else 69)))) else (if i.val < 967 then (if i.val < 965 then (if i.val < 964 then 40 else 38) else (if i.val < 966 then 71 else 38)) else (if i.val < 969 then (if i.val < 968 then 40 else 69) else (if i.val < 970 then 69 else (if i.val < 971 then 69 else 69)))))) else (if i.val < 990 then (if i.val < 981 then (if i.val < 976 then (if i.val < 974 then (if i.val < 973 then 38 else 69) else (if i.val < 975 then 71 else 69)) else (if i.val < 978 then (if i.val < 977 then 49 else 38) else (if i.val < 979 then 38 else (if i.val < 980 then 45 else 49)))) else (if i.val < 985 then (if i.val < 983 then (if i.val < 982 then 40 else 38) else (if i.val < 984 then 49 else 49)) else (if i.val < 987 then (if i.val < 986 then 13 else 49) else (if i.val < 988 then 49 else (if i.val < 989 then 38 else 38))))) else (if i.val < 999 then (if i.val < 994 then (if i.val < 992 then (if i.val < 991 then 49 else 10) else (if i.val < 993 then 38 else 49)) else (if i.val < 996 then (if i.val < 995 then 34 else 75) else (if i.val < 997 then 38 else (if i.val < 998 then 71 else 86)))) else (if i.val < 1003 then (if i.val < 1001 then (if i.val < 1000 then 52 else 6) else (if i.val < 1002 then 38 else 15)) else (if i.val < 1005 then (if i.val < 1004 then 57 else 49) else (if i.val < 1006 then 86 else (if i.val < 1007 then 84 else 5)))))))) else (if i.val < 1080 then (if i.val < 1044 then (if i.val < 1026 then (if i.val < 1017 then (if i.val < 1012 then (if i.val < 1010 then (if i.val < 1009 then 86 else 6) else (if i.val < 1011 then 32 else 31)) else (if i.val < 1014 then (if i.val < 1013 then 10 else 49) else (if i.val < 1015 then 34 else (if i.val < 1016 then 45 else 49)))) else (if i.val < 1021 then (if i.val < 1019 then (if i.val < 1018 then 31 else 34) else (if i.val < 1020 then 10 else 13)) else (if i.val < 1023 then (if i.val < 1022 then 82 else 49) else (if i.val < 1024 then 45 else (if i.val < 1025 then 13 else 69))))) else (if i.val < 1035 then (if i.val < 1030 then (if i.val < 1028 then (if i.val < 1027 then 49 else 86) else (if i.val < 1029 then 49 else 49)) else (if i.val < 1032 then (if i.val < 1031 then 84 else 13) else (if i.val < 1033 then 13 else (if i.val < 1034 then 86 else 10)))) else (if i.val < 1039 then (if i.val < 1037 then (if i.val < 1036 then 57 else 49) else (if i.val < 1038 then 49 else 38)) else (if i.val < 1041 then (if i.val < 1040 then 18 else 6) else (if i.val < 1042 then 49 else (if i.val < 1043 then 69 else 49)))))) else (if i.val < 1062 then (if i.val < 1053 then (if i.val < 1048 then (if i.val < 1046 then (if i.val < 1045 then 49 else 83) else (if i.val < 1047 then 75 else 5)) else (if i.val < 1050 then (if i.val < 1049 then 49 else 49) else (if i.val < 1051 then 13 else (if i.val < 1052 then 69 else 52)))) else (if i.val < 1057 then (if i.val < 1055 then (if i.val < 1054 then 38 else 84) else (if i.val < 1056 then 38 else 10)) else (if i.val < 1059 then (if i.val < 1058 then 49 else 84) else (if i.val < 1060 then 49 else (if i.val < 1061 then 35 else 34))))) else (if i.val < 1071 then (if i.val < 1066 then (if i.val < 1064 then (if i.val < 1063 then 38 else 71) else (if i.val < 1065 then 6 else 83)) else (if i.val < 1068 then (if i.val < 1067 then 18 else 6) else (if i.val < 1069 then 35 else (if i.val < 1070 then 57 else 35)))) else (if i.val < 1075 then (if i.val < 1073 then (if i.val < 1072 then 57 else 57) else (if i.val < 1074 then 32 else 34)) else (if i.val < 1077 then (if i.val < 1076 then 65 else 57) else (if i.val < 1078 then 32 else (if i.val < 1079 then 34 else 35))))))) else (if i.val < 1116 then (if i.val < 1098 then (if i.val < 1089 then (if i.val < 1084 then (if i.val < 1082 then (if i.val < 1081 then 57 else 65) else (if i.val < 1083 then 15 else 57)) else (if i.val < 1086 then (if i.val < 1085 then 15 else 15) else (if i.val < 1087 then 34 else (if i.val < 1088 then 34 else 57)))) else (if i.val < 1093 then (if i.val < 1091 then (if i.val < 1090 then 15 else 34) else (if i.val < 1092 then 34 else 34)) else (if i.val < 1095 then (if i.val < 1094 then 34 else 34) else (if i.val < 1096 then 15 else (if i.val < 1097 then 57 else 71))))) else (if i.val < 1107 then (if i.val < 1102 then (if i.val < 1100 then (if i.val < 1099 then 34 else 32) else (if i.val < 1101 then 6 else 38)) else (if i.val < 1104 then (if i.val < 1103 then 71 else 57) else (if i.val < 1105 then 5 else (if i.val < 1106 then 71 else 6)))) else (if i.val < 1111 then (if i.val < 1109 then (if i.val < 1108 then 69 else 69) else (if i.val < 1110 then 69 else 38)) else (if i.val < 1113 then (if i.val < 1112 then 69 else 71) else (if i.val < 1114 then 38 else (if i.val < 1115 then 75 else 69)))))) else (if i.val < 1134 then (if i.val < 1125 then (if i.val < 1120 then (if i.val < 1118 then (if i.val < 1117 then 57 else 71) else (if i.val < 1119 then 38 else 38)) else (if i.val < 1122 then (if i.val < 1121 then 69 else 38) else (if i.val < 1123 then 38 else (if i.val < 1124 then 69 else 40)))) else (if i.val < 1129 then (if i.val < 1127 then (if i.val < 1126 then 18 else 15) else (if i.val < 1128 then 71 else 5)) else (if i.val < 1131 then (if i.val < 1130 then 71 else 40) else (if i.val < 1132 then 71 else (if i.val < 1133 then 69 else 38))))) else (if i.val < 1143 then (if i.val < 1138 then (if i.val < 1136 then (if i.val < 1135 then 71 else 18) else (if i.val < 1137 then 69 else 71)) else (if i.val < 1140 then (if i.val < 1139 then 69 else 38) else (if i.val < 1141 then 40 else (if i.val < 1142 then 69 else 69)))) else (if i.val < 1147 then (if i.val < 1145 then (if i.val < 1144 then 40 else 38) else (if i.val < 1146 then 38 else 15)) else (if i.val < 1149 then (if i.val < 1148 then 5 else 13) else (if i.val < 1150 then 69 else (if i.val < 1151 then 15 else 66)))))))))))

def g32p_supplierGroup19_support : Finset (Fin 102) :=
  {0, 5, 6, 10, 13, 15, 18, 31, 32, 34, 35, 37, 38, 40, 45, 49, 52, 57, 65, 66, 69, 71, 75, 82, 83, 84, 86, 90, 94, 96, 97, 99, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup19_matrix_000 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 0 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 0 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 0 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 0 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 0 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_001 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 1 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 1 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 1 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 1 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 1 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_002 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 2 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 2 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 2 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 2 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 2 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_003 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 3 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 3 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 3 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 3 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 3 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_004 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 4 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 4 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 4 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 4 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 4 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_005 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 5 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 5 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 5 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 5 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 5 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_006 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 6 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 6 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 6 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 6 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 6 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_007 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 7 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 7 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 7 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 7 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 7 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_008 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 8 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 8 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 8 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 8 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 8 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_009 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 9 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 9 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 9 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 9 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 9 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_010 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 10 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 10 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 10 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 10 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 10 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_011 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 11 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 11 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 11 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 11 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 11 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_012 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 12 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 12 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 12 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 12 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 12 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_013 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 13 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 13 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 13 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 13 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 13 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_014 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 14 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 14 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 14 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 14 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 14 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_015 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 15 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 15 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 15 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 15 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 15 r) ∈ g32p_supplierGroup19_support := by
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

theorem g32p_supplierGroup19_matrix_016 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 16 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 16 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 16 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 16 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 16 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_017 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 17 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 17 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 17 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 17 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 17 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_018 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 18 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 18 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 18 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 18 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 18 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_019 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 19 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 19 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 19 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 19 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 19 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_020 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 20 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 20 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 20 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 20 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 20 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_021 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 21 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 21 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 21 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 21 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 21 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_022 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 22 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 22 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 22 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 22 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 22 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_023 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 23 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 23 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 23 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 23 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 23 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_024 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 24 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 24 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 24 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_024 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 24 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 24 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 24 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_024 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 24 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_025 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 25 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 25 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 25 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_025 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 25 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 25 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 25 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_025 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 25 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_026 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 26 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 26 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 26 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_026 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 26 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 26 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 26 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_026 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 26 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_027 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 27 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 27 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 27 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_027 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 27 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 27 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 27 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_027 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 27 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_028 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 28 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 28 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 28 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_028 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 28 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 28 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 28 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_028 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 28 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_029 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 29 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 29 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 29 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_029 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 29 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 29 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 29 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_029 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 29 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_030 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 30 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 30 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 30 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_030 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 30 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 30 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 30 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_030 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 30 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_031 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 31 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 31 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 31 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_031 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 31 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 31 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 31 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_031 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 31 r) ∈ g32p_supplierGroup19_support := by
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

theorem g32p_supplierGroup19_matrix_032 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 32 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 32 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 32 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_032 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 32 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 32 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 32 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_032 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 32 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_033 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 33 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 33 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 33 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_033 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 33 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 33 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 33 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_033 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 33 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_034 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 34 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 34 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 34 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_034 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 34 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 34 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 34 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_034 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 34 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_035 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 35 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 35 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 35 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_035 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 35 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 35 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 35 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_035 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 35 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_036 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 36 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 36 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 36 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_036 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 36 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 36 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 36 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_036 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 36 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_037 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 37 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 37 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 37 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_037 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 37 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 37 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 37 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_037 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 37 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_038 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 38 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 38 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 38 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_038 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 38 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 38 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 38 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_038 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 38 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_039 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 39 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 39 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 39 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_039 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 39 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 39 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 39 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_039 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 39 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_040 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 40 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 40 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 40 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_040 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 40 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 40 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 40 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_040 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 40 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_041 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 41 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 41 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 41 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_041 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 41 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 41 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 41 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_041 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 41 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_042 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 42 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 42 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 42 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_042 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 42 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 42 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 42 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_042 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 42 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_043 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 43 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 43 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 43 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_043 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 43 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 43 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 43 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_043 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 43 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_044 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 44 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 44 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 44 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_044 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 44 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 44 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 44 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_044 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 44 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_045 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 45 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 45 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 45 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_045 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 45 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 45 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 45 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_045 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 45 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_046 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 46 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 46 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 46 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_046 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 46 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 46 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 46 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_046 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 46 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_047 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 47 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 47 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 47 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_047 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 47 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 47 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 47 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_047 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 47 r) ∈ g32p_supplierGroup19_support := by
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

theorem g32p_supplierGroup19_matrix_048 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 48 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 48 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 48 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_048 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 48 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 48 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 48 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_048 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 48 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_049 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 49 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 49 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 49 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_049 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 49 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 49 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 49 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_049 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 49 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_050 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 50 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 50 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 50 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_050 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 50 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 50 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 50 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_050 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 50 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_051 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 51 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 51 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 51 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_051 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 51 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 51 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 51 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_051 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 51 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_052 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 52 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 52 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 52 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_052 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 52 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 52 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 52 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_052 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 52 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_053 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 53 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 53 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 53 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_053 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 53 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 53 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 53 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_053 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 53 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_054 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 54 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 54 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 54 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_054 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 54 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 54 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 54 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_054 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 54 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_055 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 55 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 55 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 55 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_055 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 55 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 55 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 55 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_055 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 55 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_056 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 56 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 56 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 56 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_056 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 56 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 56 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 56 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_056 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 56 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_057 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 57 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 57 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 57 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_057 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 57 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 57 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 57 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_057 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 57 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_058 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 58 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 58 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 58 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_058 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 58 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 58 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 58 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_058 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 58 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_059 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 59 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 59 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 59 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_059 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 59 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 59 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 59 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_059 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 59 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_060 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 60 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 60 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 60 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_060 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 60 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 60 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 60 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_060 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 60 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_061 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 61 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 61 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 61 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_061 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 61 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 61 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 61 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_061 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 61 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_062 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 62 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 62 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 62 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_062 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 62 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 62 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 62 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_062 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 62 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_063 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 63 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 63 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 63 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_063 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 63 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 63 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 63 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_063 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 63 r) ∈ g32p_supplierGroup19_support := by
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

theorem g32p_supplierGroup19_matrix_064 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 64 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 64 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 64 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_064 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 64 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 64 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 64 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_064 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 64 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_065 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 65 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 65 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 65 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_065 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 65 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 65 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 65 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_065 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 65 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_066 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 66 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 66 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 66 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_066 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 66 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 66 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 66 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_066 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 66 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_067 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 67 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 67 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 67 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_067 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 67 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 67 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 67 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_067 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 67 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_068 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 68 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 68 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 68 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_068 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 68 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 68 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 68 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_068 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 68 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_069 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 69 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 69 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 69 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_069 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 69 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 69 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 69 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_069 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 69 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_070 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 70 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 70 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 70 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_070 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 70 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 70 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 70 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_070 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 70 r) ∈ g32p_supplierGroup19_support := by
  decide +kernel

theorem g32p_supplierGroup19_matrix_071 : ∀ r : Fin 16,
    g32p_row24_groupNodes (g32p_finBlockIndex 1152 71 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 71 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 71 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup19_class_071 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 71 r)).1 (g32p_supplierGroup19_source (g32p_finBlockIndex 1152 71 r)).2 =
      g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 71 r) := by
  decide +kernel

theorem g32p_supplierGroup19_support_071 : ∀ r : Fin 16,
    g32p_supplierGroup19_classify (g32p_finBlockIndex 1152 71 r) ∈ g32p_supplierGroup19_support := by
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

theorem g32p_supplierGroup19_matrix (i : Fin 1152) :
    g32p_row24_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source i).1 (g32p_supplierGroup19_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row24_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup19_source i).1 (g32p_supplierGroup19_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup19_matrix_000 r
  · exact g32p_supplierGroup19_matrix_001 r
  · exact g32p_supplierGroup19_matrix_002 r
  · exact g32p_supplierGroup19_matrix_003 r
  · exact g32p_supplierGroup19_matrix_004 r
  · exact g32p_supplierGroup19_matrix_005 r
  · exact g32p_supplierGroup19_matrix_006 r
  · exact g32p_supplierGroup19_matrix_007 r
  · exact g32p_supplierGroup19_matrix_008 r
  · exact g32p_supplierGroup19_matrix_009 r
  · exact g32p_supplierGroup19_matrix_010 r
  · exact g32p_supplierGroup19_matrix_011 r
  · exact g32p_supplierGroup19_matrix_012 r
  · exact g32p_supplierGroup19_matrix_013 r
  · exact g32p_supplierGroup19_matrix_014 r
  · exact g32p_supplierGroup19_matrix_015 r
  · exact g32p_supplierGroup19_matrix_016 r
  · exact g32p_supplierGroup19_matrix_017 r
  · exact g32p_supplierGroup19_matrix_018 r
  · exact g32p_supplierGroup19_matrix_019 r
  · exact g32p_supplierGroup19_matrix_020 r
  · exact g32p_supplierGroup19_matrix_021 r
  · exact g32p_supplierGroup19_matrix_022 r
  · exact g32p_supplierGroup19_matrix_023 r
  · exact g32p_supplierGroup19_matrix_024 r
  · exact g32p_supplierGroup19_matrix_025 r
  · exact g32p_supplierGroup19_matrix_026 r
  · exact g32p_supplierGroup19_matrix_027 r
  · exact g32p_supplierGroup19_matrix_028 r
  · exact g32p_supplierGroup19_matrix_029 r
  · exact g32p_supplierGroup19_matrix_030 r
  · exact g32p_supplierGroup19_matrix_031 r
  · exact g32p_supplierGroup19_matrix_032 r
  · exact g32p_supplierGroup19_matrix_033 r
  · exact g32p_supplierGroup19_matrix_034 r
  · exact g32p_supplierGroup19_matrix_035 r
  · exact g32p_supplierGroup19_matrix_036 r
  · exact g32p_supplierGroup19_matrix_037 r
  · exact g32p_supplierGroup19_matrix_038 r
  · exact g32p_supplierGroup19_matrix_039 r
  · exact g32p_supplierGroup19_matrix_040 r
  · exact g32p_supplierGroup19_matrix_041 r
  · exact g32p_supplierGroup19_matrix_042 r
  · exact g32p_supplierGroup19_matrix_043 r
  · exact g32p_supplierGroup19_matrix_044 r
  · exact g32p_supplierGroup19_matrix_045 r
  · exact g32p_supplierGroup19_matrix_046 r
  · exact g32p_supplierGroup19_matrix_047 r
  · exact g32p_supplierGroup19_matrix_048 r
  · exact g32p_supplierGroup19_matrix_049 r
  · exact g32p_supplierGroup19_matrix_050 r
  · exact g32p_supplierGroup19_matrix_051 r
  · exact g32p_supplierGroup19_matrix_052 r
  · exact g32p_supplierGroup19_matrix_053 r
  · exact g32p_supplierGroup19_matrix_054 r
  · exact g32p_supplierGroup19_matrix_055 r
  · exact g32p_supplierGroup19_matrix_056 r
  · exact g32p_supplierGroup19_matrix_057 r
  · exact g32p_supplierGroup19_matrix_058 r
  · exact g32p_supplierGroup19_matrix_059 r
  · exact g32p_supplierGroup19_matrix_060 r
  · exact g32p_supplierGroup19_matrix_061 r
  · exact g32p_supplierGroup19_matrix_062 r
  · exact g32p_supplierGroup19_matrix_063 r
  · exact g32p_supplierGroup19_matrix_064 r
  · exact g32p_supplierGroup19_matrix_065 r
  · exact g32p_supplierGroup19_matrix_066 r
  · exact g32p_supplierGroup19_matrix_067 r
  · exact g32p_supplierGroup19_matrix_068 r
  · exact g32p_supplierGroup19_matrix_069 r
  · exact g32p_supplierGroup19_matrix_070 r
  · exact g32p_supplierGroup19_matrix_071 r

theorem g32p_supplierGroup19_class (i : Fin 1152) :
    g32p_supplierForest_classes (g32p_supplierGroup19_source i).1 (g32p_supplierGroup19_source i).2 =
      g32p_supplierGroup19_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup19_source i).1 (g32p_supplierGroup19_source i).2 =
      g32p_supplierGroup19_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup19_class_000 r
  · exact g32p_supplierGroup19_class_001 r
  · exact g32p_supplierGroup19_class_002 r
  · exact g32p_supplierGroup19_class_003 r
  · exact g32p_supplierGroup19_class_004 r
  · exact g32p_supplierGroup19_class_005 r
  · exact g32p_supplierGroup19_class_006 r
  · exact g32p_supplierGroup19_class_007 r
  · exact g32p_supplierGroup19_class_008 r
  · exact g32p_supplierGroup19_class_009 r
  · exact g32p_supplierGroup19_class_010 r
  · exact g32p_supplierGroup19_class_011 r
  · exact g32p_supplierGroup19_class_012 r
  · exact g32p_supplierGroup19_class_013 r
  · exact g32p_supplierGroup19_class_014 r
  · exact g32p_supplierGroup19_class_015 r
  · exact g32p_supplierGroup19_class_016 r
  · exact g32p_supplierGroup19_class_017 r
  · exact g32p_supplierGroup19_class_018 r
  · exact g32p_supplierGroup19_class_019 r
  · exact g32p_supplierGroup19_class_020 r
  · exact g32p_supplierGroup19_class_021 r
  · exact g32p_supplierGroup19_class_022 r
  · exact g32p_supplierGroup19_class_023 r
  · exact g32p_supplierGroup19_class_024 r
  · exact g32p_supplierGroup19_class_025 r
  · exact g32p_supplierGroup19_class_026 r
  · exact g32p_supplierGroup19_class_027 r
  · exact g32p_supplierGroup19_class_028 r
  · exact g32p_supplierGroup19_class_029 r
  · exact g32p_supplierGroup19_class_030 r
  · exact g32p_supplierGroup19_class_031 r
  · exact g32p_supplierGroup19_class_032 r
  · exact g32p_supplierGroup19_class_033 r
  · exact g32p_supplierGroup19_class_034 r
  · exact g32p_supplierGroup19_class_035 r
  · exact g32p_supplierGroup19_class_036 r
  · exact g32p_supplierGroup19_class_037 r
  · exact g32p_supplierGroup19_class_038 r
  · exact g32p_supplierGroup19_class_039 r
  · exact g32p_supplierGroup19_class_040 r
  · exact g32p_supplierGroup19_class_041 r
  · exact g32p_supplierGroup19_class_042 r
  · exact g32p_supplierGroup19_class_043 r
  · exact g32p_supplierGroup19_class_044 r
  · exact g32p_supplierGroup19_class_045 r
  · exact g32p_supplierGroup19_class_046 r
  · exact g32p_supplierGroup19_class_047 r
  · exact g32p_supplierGroup19_class_048 r
  · exact g32p_supplierGroup19_class_049 r
  · exact g32p_supplierGroup19_class_050 r
  · exact g32p_supplierGroup19_class_051 r
  · exact g32p_supplierGroup19_class_052 r
  · exact g32p_supplierGroup19_class_053 r
  · exact g32p_supplierGroup19_class_054 r
  · exact g32p_supplierGroup19_class_055 r
  · exact g32p_supplierGroup19_class_056 r
  · exact g32p_supplierGroup19_class_057 r
  · exact g32p_supplierGroup19_class_058 r
  · exact g32p_supplierGroup19_class_059 r
  · exact g32p_supplierGroup19_class_060 r
  · exact g32p_supplierGroup19_class_061 r
  · exact g32p_supplierGroup19_class_062 r
  · exact g32p_supplierGroup19_class_063 r
  · exact g32p_supplierGroup19_class_064 r
  · exact g32p_supplierGroup19_class_065 r
  · exact g32p_supplierGroup19_class_066 r
  · exact g32p_supplierGroup19_class_067 r
  · exact g32p_supplierGroup19_class_068 r
  · exact g32p_supplierGroup19_class_069 r
  · exact g32p_supplierGroup19_class_070 r
  · exact g32p_supplierGroup19_class_071 r

theorem g32p_supplierGroup19_support_mem (i : Fin 1152) :
    g32p_supplierGroup19_classify i ∈ g32p_supplierGroup19_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup19_classify i ∈ g32p_supplierGroup19_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup19_support_000 r
  · exact g32p_supplierGroup19_support_001 r
  · exact g32p_supplierGroup19_support_002 r
  · exact g32p_supplierGroup19_support_003 r
  · exact g32p_supplierGroup19_support_004 r
  · exact g32p_supplierGroup19_support_005 r
  · exact g32p_supplierGroup19_support_006 r
  · exact g32p_supplierGroup19_support_007 r
  · exact g32p_supplierGroup19_support_008 r
  · exact g32p_supplierGroup19_support_009 r
  · exact g32p_supplierGroup19_support_010 r
  · exact g32p_supplierGroup19_support_011 r
  · exact g32p_supplierGroup19_support_012 r
  · exact g32p_supplierGroup19_support_013 r
  · exact g32p_supplierGroup19_support_014 r
  · exact g32p_supplierGroup19_support_015 r
  · exact g32p_supplierGroup19_support_016 r
  · exact g32p_supplierGroup19_support_017 r
  · exact g32p_supplierGroup19_support_018 r
  · exact g32p_supplierGroup19_support_019 r
  · exact g32p_supplierGroup19_support_020 r
  · exact g32p_supplierGroup19_support_021 r
  · exact g32p_supplierGroup19_support_022 r
  · exact g32p_supplierGroup19_support_023 r
  · exact g32p_supplierGroup19_support_024 r
  · exact g32p_supplierGroup19_support_025 r
  · exact g32p_supplierGroup19_support_026 r
  · exact g32p_supplierGroup19_support_027 r
  · exact g32p_supplierGroup19_support_028 r
  · exact g32p_supplierGroup19_support_029 r
  · exact g32p_supplierGroup19_support_030 r
  · exact g32p_supplierGroup19_support_031 r
  · exact g32p_supplierGroup19_support_032 r
  · exact g32p_supplierGroup19_support_033 r
  · exact g32p_supplierGroup19_support_034 r
  · exact g32p_supplierGroup19_support_035 r
  · exact g32p_supplierGroup19_support_036 r
  · exact g32p_supplierGroup19_support_037 r
  · exact g32p_supplierGroup19_support_038 r
  · exact g32p_supplierGroup19_support_039 r
  · exact g32p_supplierGroup19_support_040 r
  · exact g32p_supplierGroup19_support_041 r
  · exact g32p_supplierGroup19_support_042 r
  · exact g32p_supplierGroup19_support_043 r
  · exact g32p_supplierGroup19_support_044 r
  · exact g32p_supplierGroup19_support_045 r
  · exact g32p_supplierGroup19_support_046 r
  · exact g32p_supplierGroup19_support_047 r
  · exact g32p_supplierGroup19_support_048 r
  · exact g32p_supplierGroup19_support_049 r
  · exact g32p_supplierGroup19_support_050 r
  · exact g32p_supplierGroup19_support_051 r
  · exact g32p_supplierGroup19_support_052 r
  · exact g32p_supplierGroup19_support_053 r
  · exact g32p_supplierGroup19_support_054 r
  · exact g32p_supplierGroup19_support_055 r
  · exact g32p_supplierGroup19_support_056 r
  · exact g32p_supplierGroup19_support_057 r
  · exact g32p_supplierGroup19_support_058 r
  · exact g32p_supplierGroup19_support_059 r
  · exact g32p_supplierGroup19_support_060 r
  · exact g32p_supplierGroup19_support_061 r
  · exact g32p_supplierGroup19_support_062 r
  · exact g32p_supplierGroup19_support_063 r
  · exact g32p_supplierGroup19_support_064 r
  · exact g32p_supplierGroup19_support_065 r
  · exact g32p_supplierGroup19_support_066 r
  · exact g32p_supplierGroup19_support_067 r
  · exact g32p_supplierGroup19_support_068 r
  · exact g32p_supplierGroup19_support_069 r
  · exact g32p_supplierGroup19_support_070 r
  · exact g32p_supplierGroup19_support_071 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row24_supplierClassifier : Fin 1152 → Fin 102 := g32p_supplierGroup19_classify

theorem g32p_row24_groupEquiv_isConj (i : Fin 1152) :
    IsConj (g32p_row24_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row24_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup19_source i).1 (g32p_supplierGroup19_source i).2
  rw [g32p_supplierGroup19_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row24_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup19_matrix i)

def g32p_row24_supplierClass (h : (g32p_recordedSuppliers 23).H) : Fin 102 :=
  g32p_row24_supplierClassifier (g32p_row24_groupEquiv.symm h)

theorem g32p_row24_supplierClass_isConj (h : (g32p_recordedSuppliers 23).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row24_supplierClass h)) := by
  have he : (g32p_row24_groupEquiv (g32p_row24_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 23).H => (a : g32p_G))
      (g32p_row24_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row24_supplierClassifier (g32p_row24_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row24_groupEquiv_isConj (g32p_row24_groupEquiv.symm h)

theorem g32p_row24_supplierClass_iff (h : (g32p_recordedSuppliers 23).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row24_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row24_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row24_supplierClass_isConj h).symm

theorem g32p_row24_supplierClass_mem_support (h : (g32p_recordedSuppliers 23).H) :
    g32p_row24_supplierClass h ∈ g32p_supplierGroup19_support :=
  g32p_supplierGroup19_support_mem (g32p_row24_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_000 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 0 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_000_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 0 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 0 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 0 9 9, g32p_row24_traceSegment_000_0000_0009, g32p_row24_traceSegment_000_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 18 9 9, g32p_row24_traceSegment_000_0018_0009, g32p_row24_traceSegment_000_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 0 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 0 18 18, g32p_row24_traceSegment_000_0000_0018, g32p_row24_traceSegment_000_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 36 9 9, g32p_row24_traceSegment_000_0036_0009, g32p_row24_traceSegment_000_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 54 9 9, g32p_row24_traceSegment_000_0054_0009, g32p_row24_traceSegment_000_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 36 18 18, g32p_row24_traceSegment_000_0036_0018, g32p_row24_traceSegment_000_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 0 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 0 36 36, g32p_row24_traceSegment_000_0000_0036, g32p_row24_traceSegment_000_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 72 9 9, g32p_row24_traceSegment_000_0072_0009, g32p_row24_traceSegment_000_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 90 9 9, g32p_row24_traceSegment_000_0090_0009, g32p_row24_traceSegment_000_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 72 18 18, g32p_row24_traceSegment_000_0072_0018, g32p_row24_traceSegment_000_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 108 9 9, g32p_row24_traceSegment_000_0108_0009, g32p_row24_traceSegment_000_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 126 9 9, g32p_row24_traceSegment_000_0126_0009, g32p_row24_traceSegment_000_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 108 18 18, g32p_row24_traceSegment_000_0108_0018, g32p_row24_traceSegment_000_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 72 36 36, g32p_row24_traceSegment_000_0072_0036, g32p_row24_traceSegment_000_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_000 0 144 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 0 72 72, g32p_row24_traceSegment_000_0000_0072, g32p_row24_traceSegment_000_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 144 9 9, g32p_row24_traceSegment_000_0144_0009, g32p_row24_traceSegment_000_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 162 9 9, g32p_row24_traceSegment_000_0162_0009, g32p_row24_traceSegment_000_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 144 18 18, g32p_row24_traceSegment_000_0144_0018, g32p_row24_traceSegment_000_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 180 9 9, g32p_row24_traceSegment_000_0180_0009, g32p_row24_traceSegment_000_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 198 9 9, g32p_row24_traceSegment_000_0198_0009, g32p_row24_traceSegment_000_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 180 18 18, g32p_row24_traceSegment_000_0180_0018, g32p_row24_traceSegment_000_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 144 36 36, g32p_row24_traceSegment_000_0144_0036, g32p_row24_traceSegment_000_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 216 9 9, g32p_row24_traceSegment_000_0216_0009, g32p_row24_traceSegment_000_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 234 9 9, g32p_row24_traceSegment_000_0234_0009, g32p_row24_traceSegment_000_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 216 18 18, g32p_row24_traceSegment_000_0216_0018, g32p_row24_traceSegment_000_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 252 9 9, g32p_row24_traceSegment_000_0252_0009, g32p_row24_traceSegment_000_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 270 9 9, g32p_row24_traceSegment_000_0270_0009, g32p_row24_traceSegment_000_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 252 18 18, g32p_row24_traceSegment_000_0252_0018, g32p_row24_traceSegment_000_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 216 36 36, g32p_row24_traceSegment_000_0216_0036, g32p_row24_traceSegment_000_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_000 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 144 72 72, g32p_row24_traceSegment_000_0144_0072, g32p_row24_traceSegment_000_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_000 0 288 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 0 144 144, g32p_row24_traceSegment_000_0000_0144, g32p_row24_traceSegment_000_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 288 9 9, g32p_row24_traceSegment_000_0288_0009, g32p_row24_traceSegment_000_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 306 9 9, g32p_row24_traceSegment_000_0306_0009, g32p_row24_traceSegment_000_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 288 18 18, g32p_row24_traceSegment_000_0288_0018, g32p_row24_traceSegment_000_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 324 9 9, g32p_row24_traceSegment_000_0324_0009, g32p_row24_traceSegment_000_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 342 9 9, g32p_row24_traceSegment_000_0342_0009, g32p_row24_traceSegment_000_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 324 18 18, g32p_row24_traceSegment_000_0324_0018, g32p_row24_traceSegment_000_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 288 36 36, g32p_row24_traceSegment_000_0288_0036, g32p_row24_traceSegment_000_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 360 9 9, g32p_row24_traceSegment_000_0360_0009, g32p_row24_traceSegment_000_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 378 9 9, g32p_row24_traceSegment_000_0378_0009, g32p_row24_traceSegment_000_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 360 18 18, g32p_row24_traceSegment_000_0360_0018, g32p_row24_traceSegment_000_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 396 9 9, g32p_row24_traceSegment_000_0396_0009, g32p_row24_traceSegment_000_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 414 9 9, g32p_row24_traceSegment_000_0414_0009, g32p_row24_traceSegment_000_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 396 18 18, g32p_row24_traceSegment_000_0396_0018, g32p_row24_traceSegment_000_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 360 36 36, g32p_row24_traceSegment_000_0360_0036, g32p_row24_traceSegment_000_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_000 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 288 72 72, g32p_row24_traceSegment_000_0288_0072, g32p_row24_traceSegment_000_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 432 9 9, g32p_row24_traceSegment_000_0432_0009, g32p_row24_traceSegment_000_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 450 9 9, g32p_row24_traceSegment_000_0450_0009, g32p_row24_traceSegment_000_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 432 18 18, g32p_row24_traceSegment_000_0432_0018, g32p_row24_traceSegment_000_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 468 9 9, g32p_row24_traceSegment_000_0468_0009, g32p_row24_traceSegment_000_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 486 9 9, g32p_row24_traceSegment_000_0486_0009, g32p_row24_traceSegment_000_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 468 18 18, g32p_row24_traceSegment_000_0468_0018, g32p_row24_traceSegment_000_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 432 36 36, g32p_row24_traceSegment_000_0432_0036, g32p_row24_traceSegment_000_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 504 9 9, g32p_row24_traceSegment_000_0504_0009, g32p_row24_traceSegment_000_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 522 9 9, g32p_row24_traceSegment_000_0522_0009, g32p_row24_traceSegment_000_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 504 18 18, g32p_row24_traceSegment_000_0504_0018, g32p_row24_traceSegment_000_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 540 9 9, g32p_row24_traceSegment_000_0540_0009, g32p_row24_traceSegment_000_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 558 9 9, g32p_row24_traceSegment_000_0558_0009, g32p_row24_traceSegment_000_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 540 18 18, g32p_row24_traceSegment_000_0540_0018, g32p_row24_traceSegment_000_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 504 36 36, g32p_row24_traceSegment_000_0504_0036, g32p_row24_traceSegment_000_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_000 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 432 72 72, g32p_row24_traceSegment_000_0432_0072, g32p_row24_traceSegment_000_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_000 288 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 288 144 144, g32p_row24_traceSegment_000_0288_0144, g32p_row24_traceSegment_000_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_000 0 576 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 0 288 288, g32p_row24_traceSegment_000_0000_0288, g32p_row24_traceSegment_000_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 576 9 9, g32p_row24_traceSegment_000_0576_0009, g32p_row24_traceSegment_000_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 594 9 9, g32p_row24_traceSegment_000_0594_0009, g32p_row24_traceSegment_000_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 576 18 18, g32p_row24_traceSegment_000_0576_0018, g32p_row24_traceSegment_000_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 612 9 9, g32p_row24_traceSegment_000_0612_0009, g32p_row24_traceSegment_000_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 630 9 9, g32p_row24_traceSegment_000_0630_0009, g32p_row24_traceSegment_000_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 612 18 18, g32p_row24_traceSegment_000_0612_0018, g32p_row24_traceSegment_000_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 576 36 36, g32p_row24_traceSegment_000_0576_0036, g32p_row24_traceSegment_000_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 648 9 9, g32p_row24_traceSegment_000_0648_0009, g32p_row24_traceSegment_000_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 666 9 9, g32p_row24_traceSegment_000_0666_0009, g32p_row24_traceSegment_000_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 648 18 18, g32p_row24_traceSegment_000_0648_0018, g32p_row24_traceSegment_000_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 684 9 9, g32p_row24_traceSegment_000_0684_0009, g32p_row24_traceSegment_000_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 702 9 9, g32p_row24_traceSegment_000_0702_0009, g32p_row24_traceSegment_000_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 684 18 18, g32p_row24_traceSegment_000_0684_0018, g32p_row24_traceSegment_000_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 648 36 36, g32p_row24_traceSegment_000_0648_0036, g32p_row24_traceSegment_000_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_000 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 576 72 72, g32p_row24_traceSegment_000_0576_0072, g32p_row24_traceSegment_000_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 720 9 9, g32p_row24_traceSegment_000_0720_0009, g32p_row24_traceSegment_000_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 738 9 9, g32p_row24_traceSegment_000_0738_0009, g32p_row24_traceSegment_000_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 720 18 18, g32p_row24_traceSegment_000_0720_0018, g32p_row24_traceSegment_000_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 756 9 9, g32p_row24_traceSegment_000_0756_0009, g32p_row24_traceSegment_000_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 774 9 9, g32p_row24_traceSegment_000_0774_0009, g32p_row24_traceSegment_000_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 756 18 18, g32p_row24_traceSegment_000_0756_0018, g32p_row24_traceSegment_000_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 720 36 36, g32p_row24_traceSegment_000_0720_0036, g32p_row24_traceSegment_000_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 792 9 9, g32p_row24_traceSegment_000_0792_0009, g32p_row24_traceSegment_000_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 810 9 9, g32p_row24_traceSegment_000_0810_0009, g32p_row24_traceSegment_000_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 792 18 18, g32p_row24_traceSegment_000_0792_0018, g32p_row24_traceSegment_000_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 828 9 9, g32p_row24_traceSegment_000_0828_0009, g32p_row24_traceSegment_000_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 846 9 9, g32p_row24_traceSegment_000_0846_0009, g32p_row24_traceSegment_000_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 828 18 18, g32p_row24_traceSegment_000_0828_0018, g32p_row24_traceSegment_000_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 792 36 36, g32p_row24_traceSegment_000_0792_0036, g32p_row24_traceSegment_000_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_000 720 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 720 72 72, g32p_row24_traceSegment_000_0720_0072, g32p_row24_traceSegment_000_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_000 576 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 576 144 144, g32p_row24_traceSegment_000_0576_0144, g32p_row24_traceSegment_000_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 864 9 9, g32p_row24_traceSegment_000_0864_0009, g32p_row24_traceSegment_000_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 882 9 9, g32p_row24_traceSegment_000_0882_0009, g32p_row24_traceSegment_000_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 864 18 18, g32p_row24_traceSegment_000_0864_0018, g32p_row24_traceSegment_000_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 900 9 9, g32p_row24_traceSegment_000_0900_0009, g32p_row24_traceSegment_000_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 918 9 9, g32p_row24_traceSegment_000_0918_0009, g32p_row24_traceSegment_000_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 900 18 18, g32p_row24_traceSegment_000_0900_0018, g32p_row24_traceSegment_000_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 864 36 36, g32p_row24_traceSegment_000_0864_0036, g32p_row24_traceSegment_000_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 936 9 9, g32p_row24_traceSegment_000_0936_0009, g32p_row24_traceSegment_000_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 954 9 9, g32p_row24_traceSegment_000_0954_0009, g32p_row24_traceSegment_000_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 936 18 18, g32p_row24_traceSegment_000_0936_0018, g32p_row24_traceSegment_000_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 972 9 9, g32p_row24_traceSegment_000_0972_0009, g32p_row24_traceSegment_000_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 990 9 9, g32p_row24_traceSegment_000_0990_0009, g32p_row24_traceSegment_000_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 972 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 972 18 18, g32p_row24_traceSegment_000_0972_0018, g32p_row24_traceSegment_000_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 936 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 936 36 36, g32p_row24_traceSegment_000_0936_0036, g32p_row24_traceSegment_000_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_000 864 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 864 72 72, g32p_row24_traceSegment_000_0864_0072, g32p_row24_traceSegment_000_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1008 9 9, g32p_row24_traceSegment_000_1008_0009, g32p_row24_traceSegment_000_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1026 9 9, g32p_row24_traceSegment_000_1026_0009, g32p_row24_traceSegment_000_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1008 18 18, g32p_row24_traceSegment_000_1008_0018, g32p_row24_traceSegment_000_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1044 9 9, g32p_row24_traceSegment_000_1044_0009, g32p_row24_traceSegment_000_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1062 9 9, g32p_row24_traceSegment_000_1062_0009, g32p_row24_traceSegment_000_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1044 18 18, g32p_row24_traceSegment_000_1044_0018, g32p_row24_traceSegment_000_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1008 36 36, g32p_row24_traceSegment_000_1008_0036, g32p_row24_traceSegment_000_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1080 9 9, g32p_row24_traceSegment_000_1080_0009, g32p_row24_traceSegment_000_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1098 9 9, g32p_row24_traceSegment_000_1098_0009, g32p_row24_traceSegment_000_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1080 18 18, g32p_row24_traceSegment_000_1080_0018, g32p_row24_traceSegment_000_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1116 9 9, g32p_row24_traceSegment_000_1116_0009, g32p_row24_traceSegment_000_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_000 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_000_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_000 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1134 9 9, g32p_row24_traceSegment_000_1134_0009, g32p_row24_traceSegment_000_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_000 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1116 18 18, g32p_row24_traceSegment_000_1116_0018, g32p_row24_traceSegment_000_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_000 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1080 36 36, g32p_row24_traceSegment_000_1080_0036, g32p_row24_traceSegment_000_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_000_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_000 1008 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 1008 72 72, g32p_row24_traceSegment_000_1008_0072, g32p_row24_traceSegment_000_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_000 864 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 864 144 144, g32p_row24_traceSegment_000_0864_0144, g32p_row24_traceSegment_000_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_000 576 576 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 576 288 288, g32p_row24_traceSegment_000_0576_0288, g32p_row24_traceSegment_000_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_000_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_000 0 1152 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_000 0 576 576, g32p_row24_traceSegment_000_0000_0576, g32p_row24_traceSegment_000_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 0 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_000_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_005 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 5 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_005_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 0 9 9, g32p_row24_traceSegment_005_0000_0009, g32p_row24_traceSegment_005_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 18 9 9, g32p_row24_traceSegment_005_0018_0009, g32p_row24_traceSegment_005_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 0 18 18, g32p_row24_traceSegment_005_0000_0018, g32p_row24_traceSegment_005_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 36 9 9, g32p_row24_traceSegment_005_0036_0009, g32p_row24_traceSegment_005_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 54 9 9, g32p_row24_traceSegment_005_0054_0009, g32p_row24_traceSegment_005_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 36 18 18, g32p_row24_traceSegment_005_0036_0018, g32p_row24_traceSegment_005_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 0 36 36, g32p_row24_traceSegment_005_0000_0036, g32p_row24_traceSegment_005_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 72 9 9, g32p_row24_traceSegment_005_0072_0009, g32p_row24_traceSegment_005_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 90 9 9, g32p_row24_traceSegment_005_0090_0009, g32p_row24_traceSegment_005_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 72 18 18, g32p_row24_traceSegment_005_0072_0018, g32p_row24_traceSegment_005_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 108 9 9, g32p_row24_traceSegment_005_0108_0009, g32p_row24_traceSegment_005_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 126 9 9, g32p_row24_traceSegment_005_0126_0009, g32p_row24_traceSegment_005_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 108 18 18, g32p_row24_traceSegment_005_0108_0018, g32p_row24_traceSegment_005_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 72 36 36, g32p_row24_traceSegment_005_0072_0036, g32p_row24_traceSegment_005_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_005 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 0 72 72, g32p_row24_traceSegment_005_0000_0072, g32p_row24_traceSegment_005_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 144 9 9, g32p_row24_traceSegment_005_0144_0009, g32p_row24_traceSegment_005_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 162 9 9, g32p_row24_traceSegment_005_0162_0009, g32p_row24_traceSegment_005_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 144 18 18, g32p_row24_traceSegment_005_0144_0018, g32p_row24_traceSegment_005_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 180 9 9, g32p_row24_traceSegment_005_0180_0009, g32p_row24_traceSegment_005_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 198 9 9, g32p_row24_traceSegment_005_0198_0009, g32p_row24_traceSegment_005_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 180 18 18, g32p_row24_traceSegment_005_0180_0018, g32p_row24_traceSegment_005_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 144 36 36, g32p_row24_traceSegment_005_0144_0036, g32p_row24_traceSegment_005_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 216 9 9, g32p_row24_traceSegment_005_0216_0009, g32p_row24_traceSegment_005_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 234 9 9, g32p_row24_traceSegment_005_0234_0009, g32p_row24_traceSegment_005_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 216 18 18, g32p_row24_traceSegment_005_0216_0018, g32p_row24_traceSegment_005_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 252 9 9, g32p_row24_traceSegment_005_0252_0009, g32p_row24_traceSegment_005_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 270 9 9, g32p_row24_traceSegment_005_0270_0009, g32p_row24_traceSegment_005_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 252 18 18, g32p_row24_traceSegment_005_0252_0018, g32p_row24_traceSegment_005_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 216 36 36, g32p_row24_traceSegment_005_0216_0036, g32p_row24_traceSegment_005_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_005 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 144 72 72, g32p_row24_traceSegment_005_0144_0072, g32p_row24_traceSegment_005_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_005 0 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 0 144 144, g32p_row24_traceSegment_005_0000_0144, g32p_row24_traceSegment_005_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 288 9 9, g32p_row24_traceSegment_005_0288_0009, g32p_row24_traceSegment_005_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 306 9 9, g32p_row24_traceSegment_005_0306_0009, g32p_row24_traceSegment_005_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 288 18 18, g32p_row24_traceSegment_005_0288_0018, g32p_row24_traceSegment_005_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 324 9 9, g32p_row24_traceSegment_005_0324_0009, g32p_row24_traceSegment_005_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 342 9 9, g32p_row24_traceSegment_005_0342_0009, g32p_row24_traceSegment_005_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 324 18 18, g32p_row24_traceSegment_005_0324_0018, g32p_row24_traceSegment_005_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 288 36 36, g32p_row24_traceSegment_005_0288_0036, g32p_row24_traceSegment_005_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 360 9 9, g32p_row24_traceSegment_005_0360_0009, g32p_row24_traceSegment_005_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 378 9 9, g32p_row24_traceSegment_005_0378_0009, g32p_row24_traceSegment_005_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 360 18 18, g32p_row24_traceSegment_005_0360_0018, g32p_row24_traceSegment_005_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 396 9 9, g32p_row24_traceSegment_005_0396_0009, g32p_row24_traceSegment_005_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 414 9 9, g32p_row24_traceSegment_005_0414_0009, g32p_row24_traceSegment_005_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 396 18 18, g32p_row24_traceSegment_005_0396_0018, g32p_row24_traceSegment_005_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 360 36 36, g32p_row24_traceSegment_005_0360_0036, g32p_row24_traceSegment_005_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_005 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 288 72 72, g32p_row24_traceSegment_005_0288_0072, g32p_row24_traceSegment_005_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 432 9 9, g32p_row24_traceSegment_005_0432_0009, g32p_row24_traceSegment_005_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 450 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 450 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 450 9 9, g32p_row24_traceSegment_005_0450_0009, g32p_row24_traceSegment_005_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 432 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 432 18 18, g32p_row24_traceSegment_005_0432_0018, g32p_row24_traceSegment_005_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 468 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 468 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 468 9 9, g32p_row24_traceSegment_005_0468_0009, g32p_row24_traceSegment_005_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 486 9 9, g32p_row24_traceSegment_005_0486_0009, g32p_row24_traceSegment_005_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 468 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 468 18 18, g32p_row24_traceSegment_005_0468_0018, g32p_row24_traceSegment_005_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 432 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 432 36 36, g32p_row24_traceSegment_005_0432_0036, g32p_row24_traceSegment_005_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 504 9 9, g32p_row24_traceSegment_005_0504_0009, g32p_row24_traceSegment_005_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 522 9 9, g32p_row24_traceSegment_005_0522_0009, g32p_row24_traceSegment_005_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 504 18 18, g32p_row24_traceSegment_005_0504_0018, g32p_row24_traceSegment_005_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 540 9 9, g32p_row24_traceSegment_005_0540_0009, g32p_row24_traceSegment_005_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 558 9 9, g32p_row24_traceSegment_005_0558_0009, g32p_row24_traceSegment_005_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 540 18 18, g32p_row24_traceSegment_005_0540_0018, g32p_row24_traceSegment_005_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 504 36 36, g32p_row24_traceSegment_005_0504_0036, g32p_row24_traceSegment_005_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_005 432 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 432 72 72, g32p_row24_traceSegment_005_0432_0072, g32p_row24_traceSegment_005_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_005 288 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 288 144 144, g32p_row24_traceSegment_005_0288_0144, g32p_row24_traceSegment_005_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_005 0 576 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 0 288 288, g32p_row24_traceSegment_005_0000_0288, g32p_row24_traceSegment_005_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 576 9 9, g32p_row24_traceSegment_005_0576_0009, g32p_row24_traceSegment_005_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 594 9 9, g32p_row24_traceSegment_005_0594_0009, g32p_row24_traceSegment_005_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 576 18 18, g32p_row24_traceSegment_005_0576_0018, g32p_row24_traceSegment_005_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 612 9 9, g32p_row24_traceSegment_005_0612_0009, g32p_row24_traceSegment_005_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 630 9 9, g32p_row24_traceSegment_005_0630_0009, g32p_row24_traceSegment_005_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 612 18 18, g32p_row24_traceSegment_005_0612_0018, g32p_row24_traceSegment_005_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 576 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 576 36 36, g32p_row24_traceSegment_005_0576_0036, g32p_row24_traceSegment_005_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 648 9 9, g32p_row24_traceSegment_005_0648_0009, g32p_row24_traceSegment_005_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 666 9 9, g32p_row24_traceSegment_005_0666_0009, g32p_row24_traceSegment_005_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 648 18 18, g32p_row24_traceSegment_005_0648_0018, g32p_row24_traceSegment_005_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 684 9 9, g32p_row24_traceSegment_005_0684_0009, g32p_row24_traceSegment_005_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 702 9 9, g32p_row24_traceSegment_005_0702_0009, g32p_row24_traceSegment_005_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 684 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 684 18 18, g32p_row24_traceSegment_005_0684_0018, g32p_row24_traceSegment_005_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 648 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 648 36 36, g32p_row24_traceSegment_005_0648_0036, g32p_row24_traceSegment_005_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_005 576 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 576 72 72, g32p_row24_traceSegment_005_0576_0072, g32p_row24_traceSegment_005_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 720 9 9, g32p_row24_traceSegment_005_0720_0009, g32p_row24_traceSegment_005_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 738 9 9, g32p_row24_traceSegment_005_0738_0009, g32p_row24_traceSegment_005_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 720 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 720 18 18, g32p_row24_traceSegment_005_0720_0018, g32p_row24_traceSegment_005_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 756 9 9, g32p_row24_traceSegment_005_0756_0009, g32p_row24_traceSegment_005_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 774 9 9, g32p_row24_traceSegment_005_0774_0009, g32p_row24_traceSegment_005_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 756 18 18, g32p_row24_traceSegment_005_0756_0018, g32p_row24_traceSegment_005_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 720 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 720 36 36, g32p_row24_traceSegment_005_0720_0036, g32p_row24_traceSegment_005_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 792 9 9, g32p_row24_traceSegment_005_0792_0009, g32p_row24_traceSegment_005_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 819 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 810 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 810 9 9, g32p_row24_traceSegment_005_0810_0009, g32p_row24_traceSegment_005_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 792 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 792 18 18, g32p_row24_traceSegment_005_0792_0018, g32p_row24_traceSegment_005_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 837 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 828 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 828 9 9, g32p_row24_traceSegment_005_0828_0009, g32p_row24_traceSegment_005_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 846 9 9, g32p_row24_traceSegment_005_0846_0009, g32p_row24_traceSegment_005_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 828 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 828 18 18, g32p_row24_traceSegment_005_0828_0018, g32p_row24_traceSegment_005_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 792 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 792 36 36, g32p_row24_traceSegment_005_0792_0036, g32p_row24_traceSegment_005_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_005 720 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 720 72 72, g32p_row24_traceSegment_005_0720_0072, g32p_row24_traceSegment_005_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_005 576 288 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 576 144 144, g32p_row24_traceSegment_005_0576_0144, g32p_row24_traceSegment_005_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 864 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 864 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 864 9 9, g32p_row24_traceSegment_005_0864_0009, g32p_row24_traceSegment_005_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 882 9 9, g32p_row24_traceSegment_005_0882_0009, g32p_row24_traceSegment_005_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 864 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 864 18 18, g32p_row24_traceSegment_005_0864_0018, g32p_row24_traceSegment_005_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 900 9 9, g32p_row24_traceSegment_005_0900_0009, g32p_row24_traceSegment_005_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 927 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 918 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 918 9 9, g32p_row24_traceSegment_005_0918_0009, g32p_row24_traceSegment_005_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 900 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 900 18 18, g32p_row24_traceSegment_005_0900_0018, g32p_row24_traceSegment_005_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 864 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 864 36 36, g32p_row24_traceSegment_005_0864_0036, g32p_row24_traceSegment_005_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 936 9 9, g32p_row24_traceSegment_005_0936_0009, g32p_row24_traceSegment_005_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 954 9 9, g32p_row24_traceSegment_005_0954_0009, g32p_row24_traceSegment_005_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 936 18 18, g32p_row24_traceSegment_005_0936_0018, g32p_row24_traceSegment_005_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 972 9 9, g32p_row24_traceSegment_005_0972_0009, g32p_row24_traceSegment_005_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 999 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 990 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 990 9 9, g32p_row24_traceSegment_005_0990_0009, g32p_row24_traceSegment_005_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 972 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 972 18 18, g32p_row24_traceSegment_005_0972_0018, g32p_row24_traceSegment_005_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 936 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 936 36 36, g32p_row24_traceSegment_005_0936_0036, g32p_row24_traceSegment_005_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_005 864 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 864 72 72, g32p_row24_traceSegment_005_0864_0072, g32p_row24_traceSegment_005_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1008 9 9, g32p_row24_traceSegment_005_1008_0009, g32p_row24_traceSegment_005_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1026 9 9, g32p_row24_traceSegment_005_1026_0009, g32p_row24_traceSegment_005_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1008 18 18, g32p_row24_traceSegment_005_1008_0018, g32p_row24_traceSegment_005_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1044 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 1044 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1044 9 9, g32p_row24_traceSegment_005_1044_0009, g32p_row24_traceSegment_005_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1062 9 9, g32p_row24_traceSegment_005_1062_0009, g32p_row24_traceSegment_005_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 1044 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1044 18 18, g32p_row24_traceSegment_005_1044_0018, g32p_row24_traceSegment_005_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 1008 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1008 36 36, g32p_row24_traceSegment_005_1008_0036, g32p_row24_traceSegment_005_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1080 9 9, g32p_row24_traceSegment_005_1080_0009, g32p_row24_traceSegment_005_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1098 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 1098 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1098 9 9, g32p_row24_traceSegment_005_1098_0009, g32p_row24_traceSegment_005_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 1080 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1080 18 18, g32p_row24_traceSegment_005_1080_0018, g32p_row24_traceSegment_005_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1125 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 1116 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1116 9 9, g32p_row24_traceSegment_005_1116_0009, g32p_row24_traceSegment_005_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_005 1143 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_005_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_005 1134 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1134 9 9, g32p_row24_traceSegment_005_1134_0009, g32p_row24_traceSegment_005_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_005 1116 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1116 18 18, g32p_row24_traceSegment_005_1116_0018, g32p_row24_traceSegment_005_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_005 1080 72 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1080 36 36, g32p_row24_traceSegment_005_1080_0036, g32p_row24_traceSegment_005_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_005_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_005 1008 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 1008 72 72, g32p_row24_traceSegment_005_1008_0072, g32p_row24_traceSegment_005_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_005 864 288 = [8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 864 144 144, g32p_row24_traceSegment_005_0864_0144, g32p_row24_traceSegment_005_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_005 576 576 = [10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 576 288 288, g32p_row24_traceSegment_005_0576_0288, g32p_row24_traceSegment_005_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_005_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_005 0 1152 = [12] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_005 0 576 576, g32p_row24_traceSegment_005_0000_0576, g32p_row24_traceSegment_005_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 5 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_005_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_006 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 6 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_006_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 0 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 9 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 0 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 0 9 9, g32p_row24_traceSegment_006_0000_0009, g32p_row24_traceSegment_006_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 18 9 9, g32p_row24_traceSegment_006_0018_0009, g32p_row24_traceSegment_006_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 0 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 0 18 18, g32p_row24_traceSegment_006_0000_0018, g32p_row24_traceSegment_006_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 36 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 45 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 36 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 36 9 9, g32p_row24_traceSegment_006_0036_0009, g32p_row24_traceSegment_006_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 54 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 54 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 54 9 9, g32p_row24_traceSegment_006_0054_0009, g32p_row24_traceSegment_006_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 36 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 36 18 18, g32p_row24_traceSegment_006_0036_0018, g32p_row24_traceSegment_006_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 0 72 = [5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 0 36 36, g32p_row24_traceSegment_006_0000_0036, g32p_row24_traceSegment_006_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 72 9 9, g32p_row24_traceSegment_006_0072_0009, g32p_row24_traceSegment_006_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 90 9 9, g32p_row24_traceSegment_006_0090_0009, g32p_row24_traceSegment_006_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 72 18 18, g32p_row24_traceSegment_006_0072_0018, g32p_row24_traceSegment_006_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 117 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 108 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 108 9 9, g32p_row24_traceSegment_006_0108_0009, g32p_row24_traceSegment_006_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 126 9 9, g32p_row24_traceSegment_006_0126_0009, g32p_row24_traceSegment_006_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 108 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 108 18 18, g32p_row24_traceSegment_006_0108_0018, g32p_row24_traceSegment_006_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 72 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 72 36 36, g32p_row24_traceSegment_006_0072_0036, g32p_row24_traceSegment_006_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_006 0 144 = [7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 0 72 72, g32p_row24_traceSegment_006_0000_0072, g32p_row24_traceSegment_006_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 144 9 9, g32p_row24_traceSegment_006_0144_0009, g32p_row24_traceSegment_006_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 162 9 9, g32p_row24_traceSegment_006_0162_0009, g32p_row24_traceSegment_006_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 144 18 18, g32p_row24_traceSegment_006_0144_0018, g32p_row24_traceSegment_006_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 180 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 180 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 180 9 9, g32p_row24_traceSegment_006_0180_0009, g32p_row24_traceSegment_006_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 198 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 198 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 198 9 9, g32p_row24_traceSegment_006_0198_0009, g32p_row24_traceSegment_006_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 180 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 180 18 18, g32p_row24_traceSegment_006_0180_0018, g32p_row24_traceSegment_006_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 144 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 144 36 36, g32p_row24_traceSegment_006_0144_0036, g32p_row24_traceSegment_006_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 216 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 216 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 216 9 9, g32p_row24_traceSegment_006_0216_0009, g32p_row24_traceSegment_006_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 234 9 9, g32p_row24_traceSegment_006_0234_0009, g32p_row24_traceSegment_006_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 216 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 216 18 18, g32p_row24_traceSegment_006_0216_0018, g32p_row24_traceSegment_006_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 252 9 9, g32p_row24_traceSegment_006_0252_0009, g32p_row24_traceSegment_006_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 270 9 9, g32p_row24_traceSegment_006_0270_0009, g32p_row24_traceSegment_006_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 252 18 18, g32p_row24_traceSegment_006_0252_0018, g32p_row24_traceSegment_006_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 216 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 216 36 36, g32p_row24_traceSegment_006_0216_0036, g32p_row24_traceSegment_006_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_006 144 144 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 144 72 72, g32p_row24_traceSegment_006_0144_0072, g32p_row24_traceSegment_006_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_006 0 288 = [11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 0 144 144, g32p_row24_traceSegment_006_0000_0144, g32p_row24_traceSegment_006_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 288 9 9, g32p_row24_traceSegment_006_0288_0009, g32p_row24_traceSegment_006_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 306 9 9, g32p_row24_traceSegment_006_0306_0009, g32p_row24_traceSegment_006_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 288 18 18, g32p_row24_traceSegment_006_0288_0018, g32p_row24_traceSegment_006_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 324 9 9, g32p_row24_traceSegment_006_0324_0009, g32p_row24_traceSegment_006_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 342 9 9, g32p_row24_traceSegment_006_0342_0009, g32p_row24_traceSegment_006_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 324 18 18, g32p_row24_traceSegment_006_0324_0018, g32p_row24_traceSegment_006_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 288 36 36, g32p_row24_traceSegment_006_0288_0036, g32p_row24_traceSegment_006_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 360 9 9, g32p_row24_traceSegment_006_0360_0009, g32p_row24_traceSegment_006_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 378 9 9, g32p_row24_traceSegment_006_0378_0009, g32p_row24_traceSegment_006_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 360 18 18, g32p_row24_traceSegment_006_0360_0018, g32p_row24_traceSegment_006_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 396 9 9, g32p_row24_traceSegment_006_0396_0009, g32p_row24_traceSegment_006_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 414 9 9, g32p_row24_traceSegment_006_0414_0009, g32p_row24_traceSegment_006_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 396 18 18, g32p_row24_traceSegment_006_0396_0018, g32p_row24_traceSegment_006_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 360 36 36, g32p_row24_traceSegment_006_0360_0036, g32p_row24_traceSegment_006_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_006 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 288 72 72, g32p_row24_traceSegment_006_0288_0072, g32p_row24_traceSegment_006_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 432 9 9, g32p_row24_traceSegment_006_0432_0009, g32p_row24_traceSegment_006_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 450 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 450 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 450 9 9, g32p_row24_traceSegment_006_0450_0009, g32p_row24_traceSegment_006_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 432 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 432 18 18, g32p_row24_traceSegment_006_0432_0018, g32p_row24_traceSegment_006_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 468 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 477 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 468 18 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 468 9 9, g32p_row24_traceSegment_006_0468_0009, g32p_row24_traceSegment_006_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 486 9 9, g32p_row24_traceSegment_006_0486_0009, g32p_row24_traceSegment_006_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 468 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 468 18 18, g32p_row24_traceSegment_006_0468_0018, g32p_row24_traceSegment_006_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 432 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 432 36 36, g32p_row24_traceSegment_006_0432_0036, g32p_row24_traceSegment_006_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 513 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 504 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 504 9 9, g32p_row24_traceSegment_006_0504_0009, g32p_row24_traceSegment_006_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 522 9 9, g32p_row24_traceSegment_006_0522_0009, g32p_row24_traceSegment_006_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 504 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 504 18 18, g32p_row24_traceSegment_006_0504_0018, g32p_row24_traceSegment_006_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 540 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 540 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 540 9 9, g32p_row24_traceSegment_006_0540_0009, g32p_row24_traceSegment_006_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 558 9 9, g32p_row24_traceSegment_006_0558_0009, g32p_row24_traceSegment_006_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 540 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 540 18 18, g32p_row24_traceSegment_006_0540_0018, g32p_row24_traceSegment_006_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 504 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 504 36 36, g32p_row24_traceSegment_006_0504_0036, g32p_row24_traceSegment_006_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_006 432 144 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 432 72 72, g32p_row24_traceSegment_006_0432_0072, g32p_row24_traceSegment_006_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_006 288 288 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 288 144 144, g32p_row24_traceSegment_006_0288_0144, g32p_row24_traceSegment_006_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_006 0 576 = [17] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 0 288 288, g32p_row24_traceSegment_006_0000_0288, g32p_row24_traceSegment_006_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 585 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 576 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 576 9 9, g32p_row24_traceSegment_006_0576_0009, g32p_row24_traceSegment_006_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 594 9 9, g32p_row24_traceSegment_006_0594_0009, g32p_row24_traceSegment_006_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 576 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 576 18 18, g32p_row24_traceSegment_006_0576_0018, g32p_row24_traceSegment_006_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 612 9 9, g32p_row24_traceSegment_006_0612_0009, g32p_row24_traceSegment_006_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 630 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 630 9 9, g32p_row24_traceSegment_006_0630_0009, g32p_row24_traceSegment_006_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 612 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 612 18 18, g32p_row24_traceSegment_006_0612_0018, g32p_row24_traceSegment_006_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 576 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 576 36 36, g32p_row24_traceSegment_006_0576_0036, g32p_row24_traceSegment_006_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 648 9 9, g32p_row24_traceSegment_006_0648_0009, g32p_row24_traceSegment_006_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 666 9 9, g32p_row24_traceSegment_006_0666_0009, g32p_row24_traceSegment_006_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 648 18 18, g32p_row24_traceSegment_006_0648_0018, g32p_row24_traceSegment_006_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 684 9 9, g32p_row24_traceSegment_006_0684_0009, g32p_row24_traceSegment_006_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 711 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 702 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 702 9 9, g32p_row24_traceSegment_006_0702_0009, g32p_row24_traceSegment_006_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 684 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 684 18 18, g32p_row24_traceSegment_006_0684_0018, g32p_row24_traceSegment_006_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 648 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 648 36 36, g32p_row24_traceSegment_006_0648_0036, g32p_row24_traceSegment_006_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_006 576 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 576 72 72, g32p_row24_traceSegment_006_0576_0072, g32p_row24_traceSegment_006_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 720 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 720 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 720 9 9, g32p_row24_traceSegment_006_0720_0009, g32p_row24_traceSegment_006_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 738 9 9, g32p_row24_traceSegment_006_0738_0009, g32p_row24_traceSegment_006_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 720 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 720 18 18, g32p_row24_traceSegment_006_0720_0018, g32p_row24_traceSegment_006_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 756 9 9, g32p_row24_traceSegment_006_0756_0009, g32p_row24_traceSegment_006_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 774 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 774 9 9, g32p_row24_traceSegment_006_0774_0009, g32p_row24_traceSegment_006_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 756 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 756 18 18, g32p_row24_traceSegment_006_0756_0018, g32p_row24_traceSegment_006_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 720 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 720 36 36, g32p_row24_traceSegment_006_0720_0036, g32p_row24_traceSegment_006_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 792 9 9, g32p_row24_traceSegment_006_0792_0009, g32p_row24_traceSegment_006_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 810 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 810 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 810 9 9, g32p_row24_traceSegment_006_0810_0009, g32p_row24_traceSegment_006_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 792 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 792 18 18, g32p_row24_traceSegment_006_0792_0018, g32p_row24_traceSegment_006_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 828 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 828 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 828 9 9, g32p_row24_traceSegment_006_0828_0009, g32p_row24_traceSegment_006_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 846 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 855 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 846 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 846 9 9, g32p_row24_traceSegment_006_0846_0009, g32p_row24_traceSegment_006_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 828 36 = [3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 828 18 18, g32p_row24_traceSegment_006_0828_0018, g32p_row24_traceSegment_006_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 792 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 792 36 36, g32p_row24_traceSegment_006_0792_0036, g32p_row24_traceSegment_006_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_006 720 144 = [5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 720 72 72, g32p_row24_traceSegment_006_0720_0072, g32p_row24_traceSegment_006_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_006 576 288 = [7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 576 144 144, g32p_row24_traceSegment_006_0576_0144, g32p_row24_traceSegment_006_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 864 9 9, g32p_row24_traceSegment_006_0864_0009, g32p_row24_traceSegment_006_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 882 9 9, g32p_row24_traceSegment_006_0882_0009, g32p_row24_traceSegment_006_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 864 18 18, g32p_row24_traceSegment_006_0864_0018, g32p_row24_traceSegment_006_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 900 9 9, g32p_row24_traceSegment_006_0900_0009, g32p_row24_traceSegment_006_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 927 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 918 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 918 9 9, g32p_row24_traceSegment_006_0918_0009, g32p_row24_traceSegment_006_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 900 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 900 18 18, g32p_row24_traceSegment_006_0900_0018, g32p_row24_traceSegment_006_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 864 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 864 36 36, g32p_row24_traceSegment_006_0864_0036, g32p_row24_traceSegment_006_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 936 9 9, g32p_row24_traceSegment_006_0936_0009, g32p_row24_traceSegment_006_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 954 9 9, g32p_row24_traceSegment_006_0954_0009, g32p_row24_traceSegment_006_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 936 18 18, g32p_row24_traceSegment_006_0936_0018, g32p_row24_traceSegment_006_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 972 9 9, g32p_row24_traceSegment_006_0972_0009, g32p_row24_traceSegment_006_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 999 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 990 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 990 9 9, g32p_row24_traceSegment_006_0990_0009, g32p_row24_traceSegment_006_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 972 36 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 972 18 18, g32p_row24_traceSegment_006_0972_0018, g32p_row24_traceSegment_006_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 936 72 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 936 36 36, g32p_row24_traceSegment_006_0936_0036, g32p_row24_traceSegment_006_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_006 864 144 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 864 72 72, g32p_row24_traceSegment_006_0864_0072, g32p_row24_traceSegment_006_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1008 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 1008 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1008 9 9, g32p_row24_traceSegment_006_1008_0009, g32p_row24_traceSegment_006_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1035 9 = [1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 1026 18 = [1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1026 9 9, g32p_row24_traceSegment_006_1026_0009, g32p_row24_traceSegment_006_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 1008 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1008 18 18, g32p_row24_traceSegment_006_1008_0018, g32p_row24_traceSegment_006_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1044 9 9, g32p_row24_traceSegment_006_1044_0009, g32p_row24_traceSegment_006_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1062 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 1062 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1062 9 9, g32p_row24_traceSegment_006_1062_0009, g32p_row24_traceSegment_006_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 1044 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1044 18 18, g32p_row24_traceSegment_006_1044_0018, g32p_row24_traceSegment_006_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 1008 72 = [4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1008 36 36, g32p_row24_traceSegment_006_1008_0036, g32p_row24_traceSegment_006_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1080 9 9, g32p_row24_traceSegment_006_1080_0009, g32p_row24_traceSegment_006_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1098 9 = [2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 1098 18 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1098 9 9, g32p_row24_traceSegment_006_1098_0009, g32p_row24_traceSegment_006_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 1080 36 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1080 18 18, g32p_row24_traceSegment_006_1080_0018, g32p_row24_traceSegment_006_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1116 9 9, g32p_row24_traceSegment_006_1116_0009, g32p_row24_traceSegment_006_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_006 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_006_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_006 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1134 9 9, g32p_row24_traceSegment_006_1134_0009, g32p_row24_traceSegment_006_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_006 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1116 18 18, g32p_row24_traceSegment_006_1116_0018, g32p_row24_traceSegment_006_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_006 1080 72 = [2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1080 36 36, g32p_row24_traceSegment_006_1080_0036, g32p_row24_traceSegment_006_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_006_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_006 1008 144 = [6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 1008 72 72, g32p_row24_traceSegment_006_1008_0072, g32p_row24_traceSegment_006_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_006 864 288 = [8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 864 144 144, g32p_row24_traceSegment_006_0864_0144, g32p_row24_traceSegment_006_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_006 576 576 = [15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 576 288 288, g32p_row24_traceSegment_006_0576_0288, g32p_row24_traceSegment_006_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_006_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_006 0 1152 = [32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_006 0 576 576, g32p_row24_traceSegment_006_0000_0576, g32p_row24_traceSegment_006_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 6 = [32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_006_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_010 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 10 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_010_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 0 9 9, g32p_row24_traceSegment_010_0000_0009, g32p_row24_traceSegment_010_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 18 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 18 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 18 9 9, g32p_row24_traceSegment_010_0018_0009, g32p_row24_traceSegment_010_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 0 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 0 18 18, g32p_row24_traceSegment_010_0000_0018, g32p_row24_traceSegment_010_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 36 9 9, g32p_row24_traceSegment_010_0036_0009, g32p_row24_traceSegment_010_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 54 9 9, g32p_row24_traceSegment_010_0054_0009, g32p_row24_traceSegment_010_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 36 18 18, g32p_row24_traceSegment_010_0036_0018, g32p_row24_traceSegment_010_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 0 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 0 36 36, g32p_row24_traceSegment_010_0000_0036, g32p_row24_traceSegment_010_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 72 9 9, g32p_row24_traceSegment_010_0072_0009, g32p_row24_traceSegment_010_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 90 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 90 9 9, g32p_row24_traceSegment_010_0090_0009, g32p_row24_traceSegment_010_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 72 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 72 18 18, g32p_row24_traceSegment_010_0072_0018, g32p_row24_traceSegment_010_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 108 9 9, g32p_row24_traceSegment_010_0108_0009, g32p_row24_traceSegment_010_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 126 9 9, g32p_row24_traceSegment_010_0126_0009, g32p_row24_traceSegment_010_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 108 18 18, g32p_row24_traceSegment_010_0108_0018, g32p_row24_traceSegment_010_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 72 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 72 36 36, g32p_row24_traceSegment_010_0072_0036, g32p_row24_traceSegment_010_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_010 0 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 0 72 72, g32p_row24_traceSegment_010_0000_0072, g32p_row24_traceSegment_010_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 144 9 9, g32p_row24_traceSegment_010_0144_0009, g32p_row24_traceSegment_010_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 162 9 9, g32p_row24_traceSegment_010_0162_0009, g32p_row24_traceSegment_010_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 144 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 144 18 18, g32p_row24_traceSegment_010_0144_0018, g32p_row24_traceSegment_010_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 180 9 9, g32p_row24_traceSegment_010_0180_0009, g32p_row24_traceSegment_010_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 198 9 9, g32p_row24_traceSegment_010_0198_0009, g32p_row24_traceSegment_010_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 180 18 18, g32p_row24_traceSegment_010_0180_0018, g32p_row24_traceSegment_010_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 144 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 144 36 36, g32p_row24_traceSegment_010_0144_0036, g32p_row24_traceSegment_010_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 216 9 9, g32p_row24_traceSegment_010_0216_0009, g32p_row24_traceSegment_010_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 234 9 9, g32p_row24_traceSegment_010_0234_0009, g32p_row24_traceSegment_010_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 216 18 18, g32p_row24_traceSegment_010_0216_0018, g32p_row24_traceSegment_010_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 252 9 9, g32p_row24_traceSegment_010_0252_0009, g32p_row24_traceSegment_010_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 270 9 9, g32p_row24_traceSegment_010_0270_0009, g32p_row24_traceSegment_010_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 252 18 18, g32p_row24_traceSegment_010_0252_0018, g32p_row24_traceSegment_010_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 216 36 36, g32p_row24_traceSegment_010_0216_0036, g32p_row24_traceSegment_010_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_010 144 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 144 72 72, g32p_row24_traceSegment_010_0144_0072, g32p_row24_traceSegment_010_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_010 0 288 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 0 144 144, g32p_row24_traceSegment_010_0000_0144, g32p_row24_traceSegment_010_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 297 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 288 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 288 9 9, g32p_row24_traceSegment_010_0288_0009, g32p_row24_traceSegment_010_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 306 9 9, g32p_row24_traceSegment_010_0306_0009, g32p_row24_traceSegment_010_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 288 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 288 18 18, g32p_row24_traceSegment_010_0288_0018, g32p_row24_traceSegment_010_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 324 9 9, g32p_row24_traceSegment_010_0324_0009, g32p_row24_traceSegment_010_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 351 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 342 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 342 9 9, g32p_row24_traceSegment_010_0342_0009, g32p_row24_traceSegment_010_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 324 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 324 18 18, g32p_row24_traceSegment_010_0324_0018, g32p_row24_traceSegment_010_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 288 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 288 36 36, g32p_row24_traceSegment_010_0288_0036, g32p_row24_traceSegment_010_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 369 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 360 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 360 9 9, g32p_row24_traceSegment_010_0360_0009, g32p_row24_traceSegment_010_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 378 9 9, g32p_row24_traceSegment_010_0378_0009, g32p_row24_traceSegment_010_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 360 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 360 18 18, g32p_row24_traceSegment_010_0360_0018, g32p_row24_traceSegment_010_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 396 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 396 9 9, g32p_row24_traceSegment_010_0396_0009, g32p_row24_traceSegment_010_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 414 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 414 9 9, g32p_row24_traceSegment_010_0414_0009, g32p_row24_traceSegment_010_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 396 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 396 18 18, g32p_row24_traceSegment_010_0396_0018, g32p_row24_traceSegment_010_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 360 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 360 36 36, g32p_row24_traceSegment_010_0360_0036, g32p_row24_traceSegment_010_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_010 288 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 288 72 72, g32p_row24_traceSegment_010_0288_0072, g32p_row24_traceSegment_010_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 432 9 9, g32p_row24_traceSegment_010_0432_0009, g32p_row24_traceSegment_010_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 450 9 9, g32p_row24_traceSegment_010_0450_0009, g32p_row24_traceSegment_010_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 432 18 18, g32p_row24_traceSegment_010_0432_0018, g32p_row24_traceSegment_010_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 468 9 9, g32p_row24_traceSegment_010_0468_0009, g32p_row24_traceSegment_010_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 486 9 9, g32p_row24_traceSegment_010_0486_0009, g32p_row24_traceSegment_010_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 468 18 18, g32p_row24_traceSegment_010_0468_0018, g32p_row24_traceSegment_010_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 432 36 36, g32p_row24_traceSegment_010_0432_0036, g32p_row24_traceSegment_010_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 504 9 9, g32p_row24_traceSegment_010_0504_0009, g32p_row24_traceSegment_010_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 531 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 522 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 522 9 9, g32p_row24_traceSegment_010_0522_0009, g32p_row24_traceSegment_010_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 504 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 504 18 18, g32p_row24_traceSegment_010_0504_0018, g32p_row24_traceSegment_010_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 540 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 549 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 540 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 540 9 9, g32p_row24_traceSegment_010_0540_0009, g32p_row24_traceSegment_010_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 558 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 567 9 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 558 18 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 558 9 9, g32p_row24_traceSegment_010_0558_0009, g32p_row24_traceSegment_010_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 540 36 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 540 18 18, g32p_row24_traceSegment_010_0540_0018, g32p_row24_traceSegment_010_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 504 72 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 504 36 36, g32p_row24_traceSegment_010_0504_0036, g32p_row24_traceSegment_010_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_010 432 144 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 432 72 72, g32p_row24_traceSegment_010_0432_0072, g32p_row24_traceSegment_010_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_010 288 288 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 288 144 144, g32p_row24_traceSegment_010_0288_0144, g32p_row24_traceSegment_010_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_010 0 576 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 0 288 288, g32p_row24_traceSegment_010_0000_0288, g32p_row24_traceSegment_010_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 585 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 576 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 576 9 9, g32p_row24_traceSegment_010_0576_0009, g32p_row24_traceSegment_010_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 594 9 9, g32p_row24_traceSegment_010_0594_0009, g32p_row24_traceSegment_010_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 576 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 576 18 18, g32p_row24_traceSegment_010_0576_0018, g32p_row24_traceSegment_010_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 612 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 621 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 612 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 612 9 9, g32p_row24_traceSegment_010_0612_0009, g32p_row24_traceSegment_010_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 630 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 630 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 630 9 9, g32p_row24_traceSegment_010_0630_0009, g32p_row24_traceSegment_010_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 612 36 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 612 18 18, g32p_row24_traceSegment_010_0612_0018, g32p_row24_traceSegment_010_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 576 72 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 576 36 36, g32p_row24_traceSegment_010_0576_0036, g32p_row24_traceSegment_010_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 657 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 648 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 648 9 9, g32p_row24_traceSegment_010_0648_0009, g32p_row24_traceSegment_010_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 666 9 9, g32p_row24_traceSegment_010_0666_0009, g32p_row24_traceSegment_010_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 648 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 648 18 18, g32p_row24_traceSegment_010_0648_0018, g32p_row24_traceSegment_010_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 684 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 684 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 684 9 9, g32p_row24_traceSegment_010_0684_0009, g32p_row24_traceSegment_010_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 702 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 711 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 702 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 702 9 9, g32p_row24_traceSegment_010_0702_0009, g32p_row24_traceSegment_010_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 684 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 684 18 18, g32p_row24_traceSegment_010_0684_0018, g32p_row24_traceSegment_010_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 648 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 648 36 36, g32p_row24_traceSegment_010_0648_0036, g32p_row24_traceSegment_010_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_010 576 144 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 576 72 72, g32p_row24_traceSegment_010_0576_0072, g32p_row24_traceSegment_010_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 729 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 720 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 720 9 9, g32p_row24_traceSegment_010_0720_0009, g32p_row24_traceSegment_010_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 738 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 738 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 738 9 9, g32p_row24_traceSegment_010_0738_0009, g32p_row24_traceSegment_010_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 720 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 720 18 18, g32p_row24_traceSegment_010_0720_0018, g32p_row24_traceSegment_010_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 765 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 756 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 756 9 9, g32p_row24_traceSegment_010_0756_0009, g32p_row24_traceSegment_010_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 774 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 774 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 774 9 9, g32p_row24_traceSegment_010_0774_0009, g32p_row24_traceSegment_010_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 756 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 756 18 18, g32p_row24_traceSegment_010_0756_0018, g32p_row24_traceSegment_010_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 720 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 720 36 36, g32p_row24_traceSegment_010_0720_0036, g32p_row24_traceSegment_010_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 792 9 9, g32p_row24_traceSegment_010_0792_0009, g32p_row24_traceSegment_010_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 810 9 9, g32p_row24_traceSegment_010_0810_0009, g32p_row24_traceSegment_010_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 792 18 18, g32p_row24_traceSegment_010_0792_0018, g32p_row24_traceSegment_010_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 828 9 9, g32p_row24_traceSegment_010_0828_0009, g32p_row24_traceSegment_010_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 846 9 9, g32p_row24_traceSegment_010_0846_0009, g32p_row24_traceSegment_010_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 828 18 18, g32p_row24_traceSegment_010_0828_0018, g32p_row24_traceSegment_010_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 792 36 36, g32p_row24_traceSegment_010_0792_0036, g32p_row24_traceSegment_010_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_010 720 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 720 72 72, g32p_row24_traceSegment_010_0720_0072, g32p_row24_traceSegment_010_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_010 576 288 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 576 144 144, g32p_row24_traceSegment_010_0576_0144, g32p_row24_traceSegment_010_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 864 9 9, g32p_row24_traceSegment_010_0864_0009, g32p_row24_traceSegment_010_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 882 9 9, g32p_row24_traceSegment_010_0882_0009, g32p_row24_traceSegment_010_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 864 18 18, g32p_row24_traceSegment_010_0864_0018, g32p_row24_traceSegment_010_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 900 9 9, g32p_row24_traceSegment_010_0900_0009, g32p_row24_traceSegment_010_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 918 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 927 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 918 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 918 9 9, g32p_row24_traceSegment_010_0918_0009, g32p_row24_traceSegment_010_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 900 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 900 18 18, g32p_row24_traceSegment_010_0900_0018, g32p_row24_traceSegment_010_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 864 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 864 36 36, g32p_row24_traceSegment_010_0864_0036, g32p_row24_traceSegment_010_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 936 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 945 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 936 18 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 936 9 9, g32p_row24_traceSegment_010_0936_0009, g32p_row24_traceSegment_010_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 954 9 9, g32p_row24_traceSegment_010_0954_0009, g32p_row24_traceSegment_010_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 936 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 936 18 18, g32p_row24_traceSegment_010_0936_0018, g32p_row24_traceSegment_010_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 972 9 9, g32p_row24_traceSegment_010_0972_0009, g32p_row24_traceSegment_010_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 990 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 990 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 990 9 9, g32p_row24_traceSegment_010_0990_0009, g32p_row24_traceSegment_010_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 972 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 972 18 18, g32p_row24_traceSegment_010_0972_0018, g32p_row24_traceSegment_010_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 936 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 936 36 36, g32p_row24_traceSegment_010_0936_0036, g32p_row24_traceSegment_010_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_010 864 144 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 864 72 72, g32p_row24_traceSegment_010_0864_0072, g32p_row24_traceSegment_010_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1008 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1017 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 1008 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1008 9 9, g32p_row24_traceSegment_010_1008_0009, g32p_row24_traceSegment_010_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1026 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 1026 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1026 9 9, g32p_row24_traceSegment_010_1026_0009, g32p_row24_traceSegment_010_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 1008 36 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1008 18 18, g32p_row24_traceSegment_010_1008_0018, g32p_row24_traceSegment_010_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1053 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 1044 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1044 9 9, g32p_row24_traceSegment_010_1044_0009, g32p_row24_traceSegment_010_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1062 9 9, g32p_row24_traceSegment_010_1062_0009, g32p_row24_traceSegment_010_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 1044 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1044 18 18, g32p_row24_traceSegment_010_1044_0018, g32p_row24_traceSegment_010_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 1008 72 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1008 36 36, g32p_row24_traceSegment_010_1008_0036, g32p_row24_traceSegment_010_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1080 9 9, g32p_row24_traceSegment_010_1080_0009, g32p_row24_traceSegment_010_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1098 9 9, g32p_row24_traceSegment_010_1098_0009, g32p_row24_traceSegment_010_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1080 18 18, g32p_row24_traceSegment_010_1080_0018, g32p_row24_traceSegment_010_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1116 9 9, g32p_row24_traceSegment_010_1116_0009, g32p_row24_traceSegment_010_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_010 1143 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_010_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_010 1134 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1134 9 9, g32p_row24_traceSegment_010_1134_0009, g32p_row24_traceSegment_010_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_010 1116 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1116 18 18, g32p_row24_traceSegment_010_1116_0018, g32p_row24_traceSegment_010_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_010 1080 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1080 36 36, g32p_row24_traceSegment_010_1080_0036, g32p_row24_traceSegment_010_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_010_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_010 1008 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 1008 72 72, g32p_row24_traceSegment_010_1008_0072, g32p_row24_traceSegment_010_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_010 864 288 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 864 144 144, g32p_row24_traceSegment_010_0864_0144, g32p_row24_traceSegment_010_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_010 576 576 = [0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 576 288 288, g32p_row24_traceSegment_010_0576_0288, g32p_row24_traceSegment_010_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_010_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_010 0 1152 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_010 0 576 576, g32p_row24_traceSegment_010_0000_0576, g32p_row24_traceSegment_010_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 10 = [0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_010_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_013 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 13 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_013_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 0 9 9, g32p_row24_traceSegment_013_0000_0009, g32p_row24_traceSegment_013_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 18 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 18 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 18 9 9, g32p_row24_traceSegment_013_0018_0009, g32p_row24_traceSegment_013_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 0 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 0 18 18, g32p_row24_traceSegment_013_0000_0018, g32p_row24_traceSegment_013_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 36 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 45 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 36 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 36 9 9, g32p_row24_traceSegment_013_0036_0009, g32p_row24_traceSegment_013_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 54 9 9, g32p_row24_traceSegment_013_0054_0009, g32p_row24_traceSegment_013_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 36 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 36 18 18, g32p_row24_traceSegment_013_0036_0018, g32p_row24_traceSegment_013_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 0 72 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 0 36 36, g32p_row24_traceSegment_013_0000_0036, g32p_row24_traceSegment_013_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 72 9 9, g32p_row24_traceSegment_013_0072_0009, g32p_row24_traceSegment_013_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 90 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 99 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 90 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 90 9 9, g32p_row24_traceSegment_013_0090_0009, g32p_row24_traceSegment_013_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 72 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 72 18 18, g32p_row24_traceSegment_013_0072_0018, g32p_row24_traceSegment_013_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 108 9 9, g32p_row24_traceSegment_013_0108_0009, g32p_row24_traceSegment_013_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 126 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 126 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 126 9 9, g32p_row24_traceSegment_013_0126_0009, g32p_row24_traceSegment_013_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 108 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 108 18 18, g32p_row24_traceSegment_013_0108_0018, g32p_row24_traceSegment_013_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 72 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 72 36 36, g32p_row24_traceSegment_013_0072_0036, g32p_row24_traceSegment_013_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_013 0 144 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 0 72 72, g32p_row24_traceSegment_013_0000_0072, g32p_row24_traceSegment_013_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 144 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 153 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 144 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 144 9 9, g32p_row24_traceSegment_013_0144_0009, g32p_row24_traceSegment_013_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 171 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 162 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 162 9 9, g32p_row24_traceSegment_013_0162_0009, g32p_row24_traceSegment_013_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 144 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 144 18 18, g32p_row24_traceSegment_013_0144_0018, g32p_row24_traceSegment_013_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 189 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 180 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 180 9 9, g32p_row24_traceSegment_013_0180_0009, g32p_row24_traceSegment_013_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 207 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 198 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 198 9 9, g32p_row24_traceSegment_013_0198_0009, g32p_row24_traceSegment_013_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 180 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 180 18 18, g32p_row24_traceSegment_013_0180_0018, g32p_row24_traceSegment_013_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 144 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 144 36 36, g32p_row24_traceSegment_013_0144_0036, g32p_row24_traceSegment_013_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 225 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 216 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 216 9 9, g32p_row24_traceSegment_013_0216_0009, g32p_row24_traceSegment_013_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 234 9 = [0, 0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 243 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 234 18 = [0, 0, 1, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 234 9 9, g32p_row24_traceSegment_013_0234_0009, g32p_row24_traceSegment_013_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 216 36 = [0, 0, 2, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 216 18 18, g32p_row24_traceSegment_013_0216_0018, g32p_row24_traceSegment_013_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 252 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 252 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 252 9 9, g32p_row24_traceSegment_013_0252_0009, g32p_row24_traceSegment_013_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 270 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 279 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 270 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 270 9 9, g32p_row24_traceSegment_013_0270_0009, g32p_row24_traceSegment_013_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 252 36 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 252 18 18, g32p_row24_traceSegment_013_0252_0018, g32p_row24_traceSegment_013_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 216 72 = [0, 0, 3, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 216 36 36, g32p_row24_traceSegment_013_0216_0036, g32p_row24_traceSegment_013_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_013 144 144 = [0, 0, 6, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 144 72 72, g32p_row24_traceSegment_013_0144_0072, g32p_row24_traceSegment_013_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_013 0 288 = [0, 0, 9, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 0 144 144, g32p_row24_traceSegment_013_0000_0144, g32p_row24_traceSegment_013_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 288 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 297 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 288 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 288 9 9, g32p_row24_traceSegment_013_0288_0009, g32p_row24_traceSegment_013_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 306 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 306 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 306 9 9, g32p_row24_traceSegment_013_0306_0009, g32p_row24_traceSegment_013_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 288 36 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 288 18 18, g32p_row24_traceSegment_013_0288_0018, g32p_row24_traceSegment_013_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 324 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 324 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 324 9 9, g32p_row24_traceSegment_013_0324_0009, g32p_row24_traceSegment_013_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 351 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 342 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 342 9 9, g32p_row24_traceSegment_013_0342_0009, g32p_row24_traceSegment_013_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 324 36 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 324 18 18, g32p_row24_traceSegment_013_0324_0018, g32p_row24_traceSegment_013_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 288 72 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 288 36 36, g32p_row24_traceSegment_013_0288_0036, g32p_row24_traceSegment_013_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 369 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 360 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 360 9 9, g32p_row24_traceSegment_013_0360_0009, g32p_row24_traceSegment_013_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 378 9 9, g32p_row24_traceSegment_013_0378_0009, g32p_row24_traceSegment_013_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 360 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 360 18 18, g32p_row24_traceSegment_013_0360_0018, g32p_row24_traceSegment_013_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 396 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 405 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 396 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 396 9 9, g32p_row24_traceSegment_013_0396_0009, g32p_row24_traceSegment_013_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 414 9 = [0, 0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 423 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 414 18 = [0, 0, 1, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 414 9 9, g32p_row24_traceSegment_013_0414_0009, g32p_row24_traceSegment_013_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 396 36 = [0, 0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 396 18 18, g32p_row24_traceSegment_013_0396_0018, g32p_row24_traceSegment_013_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 360 72 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 360 36 36, g32p_row24_traceSegment_013_0360_0036, g32p_row24_traceSegment_013_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_013 288 144 = [0, 0, 4, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 288 72 72, g32p_row24_traceSegment_013_0288_0072, g32p_row24_traceSegment_013_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 432 9 9, g32p_row24_traceSegment_013_0432_0009, g32p_row24_traceSegment_013_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 450 9 9, g32p_row24_traceSegment_013_0450_0009, g32p_row24_traceSegment_013_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 432 18 18, g32p_row24_traceSegment_013_0432_0018, g32p_row24_traceSegment_013_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 468 9 9, g32p_row24_traceSegment_013_0468_0009, g32p_row24_traceSegment_013_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 495 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 486 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 486 9 9, g32p_row24_traceSegment_013_0486_0009, g32p_row24_traceSegment_013_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 468 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 468 18 18, g32p_row24_traceSegment_013_0468_0018, g32p_row24_traceSegment_013_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 432 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 432 36 36, g32p_row24_traceSegment_013_0432_0036, g32p_row24_traceSegment_013_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 504 9 9, g32p_row24_traceSegment_013_0504_0009, g32p_row24_traceSegment_013_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 522 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 522 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 522 9 9, g32p_row24_traceSegment_013_0522_0009, g32p_row24_traceSegment_013_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 504 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 504 18 18, g32p_row24_traceSegment_013_0504_0018, g32p_row24_traceSegment_013_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 540 9 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 549 9 = [0, 0, 1, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 540 18 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 540 9 9, g32p_row24_traceSegment_013_0540_0009, g32p_row24_traceSegment_013_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 558 9 9, g32p_row24_traceSegment_013_0558_0009, g32p_row24_traceSegment_013_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 540 36 = [0, 0, 1, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 540 18 18, g32p_row24_traceSegment_013_0540_0018, g32p_row24_traceSegment_013_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 504 72 = [0, 0, 2, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 504 36 36, g32p_row24_traceSegment_013_0504_0036, g32p_row24_traceSegment_013_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_013 432 144 = [0, 0, 3, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 432 72 72, g32p_row24_traceSegment_013_0432_0072, g32p_row24_traceSegment_013_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_013 288 288 = [0, 0, 7, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 288 144 144, g32p_row24_traceSegment_013_0288_0144, g32p_row24_traceSegment_013_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_013 0 576 = [0, 0, 16, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 0 288 288, g32p_row24_traceSegment_013_0000_0288, g32p_row24_traceSegment_013_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 576 9 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 585 9 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 576 18 = [0, 0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 576 9 9, g32p_row24_traceSegment_013_0576_0009, g32p_row24_traceSegment_013_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 594 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 594 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 594 9 9, g32p_row24_traceSegment_013_0594_0009, g32p_row24_traceSegment_013_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 576 36 = [0, 0, 5, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 576 18 18, g32p_row24_traceSegment_013_0576_0018, g32p_row24_traceSegment_013_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 612 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 621 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 612 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 612 9 9, g32p_row24_traceSegment_013_0612_0009, g32p_row24_traceSegment_013_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 630 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 639 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 630 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 630 9 9, g32p_row24_traceSegment_013_0630_0009, g32p_row24_traceSegment_013_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 612 36 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 612 18 18, g32p_row24_traceSegment_013_0612_0018, g32p_row24_traceSegment_013_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 576 72 = [0, 0, 7, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 576 36 36, g32p_row24_traceSegment_013_0576_0036, g32p_row24_traceSegment_013_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 648 9 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 657 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 648 18 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 648 9 9, g32p_row24_traceSegment_013_0648_0009, g32p_row24_traceSegment_013_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 666 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 666 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 666 9 9, g32p_row24_traceSegment_013_0666_0009, g32p_row24_traceSegment_013_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 648 36 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 648 18 18, g32p_row24_traceSegment_013_0648_0018, g32p_row24_traceSegment_013_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 684 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 693 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 684 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 684 9 9, g32p_row24_traceSegment_013_0684_0009, g32p_row24_traceSegment_013_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 711 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 702 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 702 9 9, g32p_row24_traceSegment_013_0702_0009, g32p_row24_traceSegment_013_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 684 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 684 18 18, g32p_row24_traceSegment_013_0684_0018, g32p_row24_traceSegment_013_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 648 72 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 648 36 36, g32p_row24_traceSegment_013_0648_0036, g32p_row24_traceSegment_013_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_013 576 144 = [0, 0, 10, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 576 72 72, g32p_row24_traceSegment_013_0576_0072, g32p_row24_traceSegment_013_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 720 9 = [0, 0, 2, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 720 18 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 720 9 9, g32p_row24_traceSegment_013_0720_0009, g32p_row24_traceSegment_013_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 747 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 738 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 738 9 9, g32p_row24_traceSegment_013_0738_0009, g32p_row24_traceSegment_013_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 720 36 = [0, 0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 720 18 18, g32p_row24_traceSegment_013_0720_0018, g32p_row24_traceSegment_013_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 756 9 9, g32p_row24_traceSegment_013_0756_0009, g32p_row24_traceSegment_013_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 774 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 783 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 774 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 774 9 9, g32p_row24_traceSegment_013_0774_0009, g32p_row24_traceSegment_013_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 756 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 756 18 18, g32p_row24_traceSegment_013_0756_0018, g32p_row24_traceSegment_013_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 720 72 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 720 36 36, g32p_row24_traceSegment_013_0720_0036, g32p_row24_traceSegment_013_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 792 9 9, g32p_row24_traceSegment_013_0792_0009, g32p_row24_traceSegment_013_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 810 9 9, g32p_row24_traceSegment_013_0810_0009, g32p_row24_traceSegment_013_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 792 18 18, g32p_row24_traceSegment_013_0792_0018, g32p_row24_traceSegment_013_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 828 9 9, g32p_row24_traceSegment_013_0828_0009, g32p_row24_traceSegment_013_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 846 9 9, g32p_row24_traceSegment_013_0846_0009, g32p_row24_traceSegment_013_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 828 18 18, g32p_row24_traceSegment_013_0828_0018, g32p_row24_traceSegment_013_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 792 36 36, g32p_row24_traceSegment_013_0792_0036, g32p_row24_traceSegment_013_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_013 720 144 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 720 72 72, g32p_row24_traceSegment_013_0720_0072, g32p_row24_traceSegment_013_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_013 576 288 = [0, 0, 13, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 576 144 144, g32p_row24_traceSegment_013_0576_0144, g32p_row24_traceSegment_013_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 864 9 9, g32p_row24_traceSegment_013_0864_0009, g32p_row24_traceSegment_013_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 882 9 9, g32p_row24_traceSegment_013_0882_0009, g32p_row24_traceSegment_013_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 864 18 18, g32p_row24_traceSegment_013_0864_0018, g32p_row24_traceSegment_013_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 900 9 9, g32p_row24_traceSegment_013_0900_0009, g32p_row24_traceSegment_013_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 927 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 918 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 918 9 9, g32p_row24_traceSegment_013_0918_0009, g32p_row24_traceSegment_013_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 900 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 900 18 18, g32p_row24_traceSegment_013_0900_0018, g32p_row24_traceSegment_013_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 864 72 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 864 36 36, g32p_row24_traceSegment_013_0864_0036, g32p_row24_traceSegment_013_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 945 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 936 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 936 9 9, g32p_row24_traceSegment_013_0936_0009, g32p_row24_traceSegment_013_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 954 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 954 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 954 9 9, g32p_row24_traceSegment_013_0954_0009, g32p_row24_traceSegment_013_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 936 36 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 936 18 18, g32p_row24_traceSegment_013_0936_0018, g32p_row24_traceSegment_013_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 981 9 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 972 18 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 972 9 9, g32p_row24_traceSegment_013_0972_0009, g32p_row24_traceSegment_013_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 999 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 990 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 990 9 9, g32p_row24_traceSegment_013_0990_0009, g32p_row24_traceSegment_013_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 972 36 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 972 18 18, g32p_row24_traceSegment_013_0972_0018, g32p_row24_traceSegment_013_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 936 72 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 936 36 36, g32p_row24_traceSegment_013_0936_0036, g32p_row24_traceSegment_013_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_013 864 144 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 864 72 72, g32p_row24_traceSegment_013_0864_0072, g32p_row24_traceSegment_013_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1017 9 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 1008 18 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1008 9 9, g32p_row24_traceSegment_013_1008_0009, g32p_row24_traceSegment_013_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1026 9 = [0, 0, 1, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 1026 18 = [0, 0, 1, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1026 9 9, g32p_row24_traceSegment_013_1026_0009, g32p_row24_traceSegment_013_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 1008 36 = [0, 0, 3, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1008 18 18, g32p_row24_traceSegment_013_1008_0018, g32p_row24_traceSegment_013_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1044 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 1044 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1044 9 9, g32p_row24_traceSegment_013_1044_0009, g32p_row24_traceSegment_013_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1062 9 9, g32p_row24_traceSegment_013_1062_0009, g32p_row24_traceSegment_013_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 1044 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1044 18 18, g32p_row24_traceSegment_013_1044_0018, g32p_row24_traceSegment_013_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 1008 72 = [0, 0, 3, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1008 36 36, g32p_row24_traceSegment_013_1008_0036, g32p_row24_traceSegment_013_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1080 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1089 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 1080 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1080 9 9, g32p_row24_traceSegment_013_1080_0009, g32p_row24_traceSegment_013_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1098 9 9, g32p_row24_traceSegment_013_1098_0009, g32p_row24_traceSegment_013_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 1080 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1080 18 18, g32p_row24_traceSegment_013_1080_0018, g32p_row24_traceSegment_013_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1125 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 1116 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1116 9 9, g32p_row24_traceSegment_013_1116_0009, g32p_row24_traceSegment_013_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_013 1143 9 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_013_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_013 1134 18 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1134 9 9, g32p_row24_traceSegment_013_1134_0009, g32p_row24_traceSegment_013_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_013 1116 36 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1116 18 18, g32p_row24_traceSegment_013_1116_0018, g32p_row24_traceSegment_013_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_013 1080 72 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1080 36 36, g32p_row24_traceSegment_013_1080_0036, g32p_row24_traceSegment_013_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_013_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_013 1008 144 = [0, 0, 3, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 1008 72 72, g32p_row24_traceSegment_013_1008_0072, g32p_row24_traceSegment_013_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_013 864 288 = [0, 0, 7, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 864 144 144, g32p_row24_traceSegment_013_0864_0144, g32p_row24_traceSegment_013_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_013 576 576 = [0, 0, 20, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 576 288 288, g32p_row24_traceSegment_013_0576_0288, g32p_row24_traceSegment_013_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_013_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_013 0 1152 = [0, 0, 36, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_013 0 576 576, g32p_row24_traceSegment_013_0000_0576, g32p_row24_traceSegment_013_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 13 = [0, 0, 36, 0, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_013_0000_1152

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row24_traceSegment_015 (k : ℕ) : List ℤ :=
  if g32p_row24_supplierClassifier (Fin.ofNat 1152 k) = 15 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row24_characterValues (Fin.ofNat 1152 k))).val 1 else []

private theorem g32p_row24_traceSegment_015_0000_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 0 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0009_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 9 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0000_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 0 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 0 9 9, g32p_row24_traceSegment_015_0000_0009, g32p_row24_traceSegment_015_0009_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0018_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 18 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0027_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 27 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0018_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 18 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 18 9 9, g32p_row24_traceSegment_015_0018_0009, g32p_row24_traceSegment_015_0027_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0000_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 0 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 0 18 18, g32p_row24_traceSegment_015_0000_0018, g32p_row24_traceSegment_015_0018_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0036_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 36 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0045_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 45 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0036_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 36 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 36 9 9, g32p_row24_traceSegment_015_0036_0009, g32p_row24_traceSegment_015_0045_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0054_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 54 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0063_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 63 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0054_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 54 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 54 9 9, g32p_row24_traceSegment_015_0054_0009, g32p_row24_traceSegment_015_0063_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0036_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 36 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 36 18 18, g32p_row24_traceSegment_015_0036_0018, g32p_row24_traceSegment_015_0054_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0000_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 0 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 0 36 36, g32p_row24_traceSegment_015_0000_0036, g32p_row24_traceSegment_015_0036_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0072_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 72 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0081_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 81 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0072_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 72 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 72 9 9, g32p_row24_traceSegment_015_0072_0009, g32p_row24_traceSegment_015_0081_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0090_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 90 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0099_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 99 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0090_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 90 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 90 9 9, g32p_row24_traceSegment_015_0090_0009, g32p_row24_traceSegment_015_0099_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0072_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 72 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 72 18 18, g32p_row24_traceSegment_015_0072_0018, g32p_row24_traceSegment_015_0090_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0108_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 108 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0117_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 117 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0108_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 108 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 108 9 9, g32p_row24_traceSegment_015_0108_0009, g32p_row24_traceSegment_015_0117_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0126_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 126 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0135_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 135 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0126_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 126 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 126 9 9, g32p_row24_traceSegment_015_0126_0009, g32p_row24_traceSegment_015_0135_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0108_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 108 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 108 18 18, g32p_row24_traceSegment_015_0108_0018, g32p_row24_traceSegment_015_0126_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0072_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 72 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 72 36 36, g32p_row24_traceSegment_015_0072_0036, g32p_row24_traceSegment_015_0108_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0000_0144 : g32p_coeffSegment g32p_row24_traceSegment_015 0 144 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 0 72 72, g32p_row24_traceSegment_015_0000_0072, g32p_row24_traceSegment_015_0072_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0144_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 144 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0153_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 153 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0144_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 144 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 144 9 9, g32p_row24_traceSegment_015_0144_0009, g32p_row24_traceSegment_015_0153_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0162_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 162 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0171_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 171 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0162_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 162 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 162 9 9, g32p_row24_traceSegment_015_0162_0009, g32p_row24_traceSegment_015_0171_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0144_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 144 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 144 18 18, g32p_row24_traceSegment_015_0144_0018, g32p_row24_traceSegment_015_0162_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0180_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 180 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0189_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 189 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0180_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 180 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 180 9 9, g32p_row24_traceSegment_015_0180_0009, g32p_row24_traceSegment_015_0189_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0198_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 198 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0207_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 207 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0198_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 198 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 198 9 9, g32p_row24_traceSegment_015_0198_0009, g32p_row24_traceSegment_015_0207_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0180_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 180 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 180 18 18, g32p_row24_traceSegment_015_0180_0018, g32p_row24_traceSegment_015_0198_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0144_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 144 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 144 36 36, g32p_row24_traceSegment_015_0144_0036, g32p_row24_traceSegment_015_0180_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0216_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 216 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0225_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 225 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0216_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 216 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 216 9 9, g32p_row24_traceSegment_015_0216_0009, g32p_row24_traceSegment_015_0225_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0234_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 234 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0243_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 243 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0234_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 234 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 234 9 9, g32p_row24_traceSegment_015_0234_0009, g32p_row24_traceSegment_015_0243_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0216_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 216 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 216 18 18, g32p_row24_traceSegment_015_0216_0018, g32p_row24_traceSegment_015_0234_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0252_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 252 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0261_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 261 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0252_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 252 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 252 9 9, g32p_row24_traceSegment_015_0252_0009, g32p_row24_traceSegment_015_0261_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0270_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 270 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0279_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 279 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0270_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 270 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 270 9 9, g32p_row24_traceSegment_015_0270_0009, g32p_row24_traceSegment_015_0279_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0252_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 252 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 252 18 18, g32p_row24_traceSegment_015_0252_0018, g32p_row24_traceSegment_015_0270_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0216_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 216 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 216 36 36, g32p_row24_traceSegment_015_0216_0036, g32p_row24_traceSegment_015_0252_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0144_0144 : g32p_coeffSegment g32p_row24_traceSegment_015 144 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 144 72 72, g32p_row24_traceSegment_015_0144_0072, g32p_row24_traceSegment_015_0216_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0000_0288 : g32p_coeffSegment g32p_row24_traceSegment_015 0 288 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 0 144 144, g32p_row24_traceSegment_015_0000_0144, g32p_row24_traceSegment_015_0144_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0288_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 288 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0297_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 297 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0288_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 288 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 288 9 9, g32p_row24_traceSegment_015_0288_0009, g32p_row24_traceSegment_015_0297_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0306_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 306 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0315_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 315 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0306_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 306 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 306 9 9, g32p_row24_traceSegment_015_0306_0009, g32p_row24_traceSegment_015_0315_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0288_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 288 36 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 288 18 18, g32p_row24_traceSegment_015_0288_0018, g32p_row24_traceSegment_015_0306_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0324_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 324 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0333_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 333 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0324_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 324 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 324 9 9, g32p_row24_traceSegment_015_0324_0009, g32p_row24_traceSegment_015_0333_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0342_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 342 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0351_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 351 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0342_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 342 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 342 9 9, g32p_row24_traceSegment_015_0342_0009, g32p_row24_traceSegment_015_0351_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0324_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 324 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 324 18 18, g32p_row24_traceSegment_015_0324_0018, g32p_row24_traceSegment_015_0342_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0288_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 288 72 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 288 36 36, g32p_row24_traceSegment_015_0288_0036, g32p_row24_traceSegment_015_0324_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0360_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 360 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0369_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 369 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0360_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 360 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 360 9 9, g32p_row24_traceSegment_015_0360_0009, g32p_row24_traceSegment_015_0369_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0378_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 378 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0387_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 387 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0378_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 378 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 378 9 9, g32p_row24_traceSegment_015_0378_0009, g32p_row24_traceSegment_015_0387_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0360_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 360 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 360 18 18, g32p_row24_traceSegment_015_0360_0018, g32p_row24_traceSegment_015_0378_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0396_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 396 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0405_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 405 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0396_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 396 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 396 9 9, g32p_row24_traceSegment_015_0396_0009, g32p_row24_traceSegment_015_0405_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0414_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 414 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0423_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 423 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0414_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 414 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 414 9 9, g32p_row24_traceSegment_015_0414_0009, g32p_row24_traceSegment_015_0423_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0396_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 396 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 396 18 18, g32p_row24_traceSegment_015_0396_0018, g32p_row24_traceSegment_015_0414_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0360_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 360 72 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 360 36 36, g32p_row24_traceSegment_015_0360_0036, g32p_row24_traceSegment_015_0396_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0288_0144 : g32p_coeffSegment g32p_row24_traceSegment_015 288 144 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 288 72 72, g32p_row24_traceSegment_015_0288_0072, g32p_row24_traceSegment_015_0360_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0432_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 432 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0441_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 441 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0432_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 432 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 432 9 9, g32p_row24_traceSegment_015_0432_0009, g32p_row24_traceSegment_015_0441_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0450_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 450 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0459_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 459 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0450_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 450 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 450 9 9, g32p_row24_traceSegment_015_0450_0009, g32p_row24_traceSegment_015_0459_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0432_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 432 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 432 18 18, g32p_row24_traceSegment_015_0432_0018, g32p_row24_traceSegment_015_0450_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0468_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 468 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0477_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 477 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0468_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 468 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 468 9 9, g32p_row24_traceSegment_015_0468_0009, g32p_row24_traceSegment_015_0477_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0486_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 486 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0495_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 495 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0486_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 486 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 486 9 9, g32p_row24_traceSegment_015_0486_0009, g32p_row24_traceSegment_015_0495_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0468_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 468 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 468 18 18, g32p_row24_traceSegment_015_0468_0018, g32p_row24_traceSegment_015_0486_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0432_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 432 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 432 36 36, g32p_row24_traceSegment_015_0432_0036, g32p_row24_traceSegment_015_0468_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0504_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 504 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0513_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 513 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0504_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 504 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 504 9 9, g32p_row24_traceSegment_015_0504_0009, g32p_row24_traceSegment_015_0513_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0522_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 522 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0531_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 531 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0522_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 522 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 522 9 9, g32p_row24_traceSegment_015_0522_0009, g32p_row24_traceSegment_015_0531_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0504_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 504 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 504 18 18, g32p_row24_traceSegment_015_0504_0018, g32p_row24_traceSegment_015_0522_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0540_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 540 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0549_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 549 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0540_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 540 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 540 9 9, g32p_row24_traceSegment_015_0540_0009, g32p_row24_traceSegment_015_0549_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0558_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 558 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0567_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 567 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0558_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 558 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 558 9 9, g32p_row24_traceSegment_015_0558_0009, g32p_row24_traceSegment_015_0567_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0540_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 540 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 540 18 18, g32p_row24_traceSegment_015_0540_0018, g32p_row24_traceSegment_015_0558_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0504_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 504 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 504 36 36, g32p_row24_traceSegment_015_0504_0036, g32p_row24_traceSegment_015_0540_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0432_0144 : g32p_coeffSegment g32p_row24_traceSegment_015 432 144 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 432 72 72, g32p_row24_traceSegment_015_0432_0072, g32p_row24_traceSegment_015_0504_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0288_0288 : g32p_coeffSegment g32p_row24_traceSegment_015 288 288 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 288 144 144, g32p_row24_traceSegment_015_0288_0144, g32p_row24_traceSegment_015_0432_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0000_0576 : g32p_coeffSegment g32p_row24_traceSegment_015 0 576 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 0 288 288, g32p_row24_traceSegment_015_0000_0288, g32p_row24_traceSegment_015_0288_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0576_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 576 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0585_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 585 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0576_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 576 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 576 9 9, g32p_row24_traceSegment_015_0576_0009, g32p_row24_traceSegment_015_0585_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0594_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 594 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0603_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 603 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0594_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 594 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 594 9 9, g32p_row24_traceSegment_015_0594_0009, g32p_row24_traceSegment_015_0603_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0576_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 576 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 576 18 18, g32p_row24_traceSegment_015_0576_0018, g32p_row24_traceSegment_015_0594_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0612_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 612 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0621_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 621 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0612_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 612 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 612 9 9, g32p_row24_traceSegment_015_0612_0009, g32p_row24_traceSegment_015_0621_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0630_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 630 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0639_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 639 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0630_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 630 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 630 9 9, g32p_row24_traceSegment_015_0630_0009, g32p_row24_traceSegment_015_0639_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0612_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 612 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 612 18 18, g32p_row24_traceSegment_015_0612_0018, g32p_row24_traceSegment_015_0630_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0576_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 576 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 576 36 36, g32p_row24_traceSegment_015_0576_0036, g32p_row24_traceSegment_015_0612_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0648_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 648 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0657_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 657 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0648_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 648 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 648 9 9, g32p_row24_traceSegment_015_0648_0009, g32p_row24_traceSegment_015_0657_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0666_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 666 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0675_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 675 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0666_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 666 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 666 9 9, g32p_row24_traceSegment_015_0666_0009, g32p_row24_traceSegment_015_0675_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0648_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 648 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 648 18 18, g32p_row24_traceSegment_015_0648_0018, g32p_row24_traceSegment_015_0666_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0684_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 684 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0693_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 693 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0684_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 684 18 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 684 9 9, g32p_row24_traceSegment_015_0684_0009, g32p_row24_traceSegment_015_0693_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0702_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 702 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0711_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 711 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0702_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 702 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 702 9 9, g32p_row24_traceSegment_015_0702_0009, g32p_row24_traceSegment_015_0711_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0684_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 684 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 684 18 18, g32p_row24_traceSegment_015_0684_0018, g32p_row24_traceSegment_015_0702_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0648_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 648 72 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 648 36 36, g32p_row24_traceSegment_015_0648_0036, g32p_row24_traceSegment_015_0684_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0576_0144 : g32p_coeffSegment g32p_row24_traceSegment_015 576 144 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 576 72 72, g32p_row24_traceSegment_015_0576_0072, g32p_row24_traceSegment_015_0648_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0720_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 720 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0729_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 729 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0720_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 720 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 720 9 9, g32p_row24_traceSegment_015_0720_0009, g32p_row24_traceSegment_015_0729_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0738_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 738 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0747_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 747 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0738_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 738 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 738 9 9, g32p_row24_traceSegment_015_0738_0009, g32p_row24_traceSegment_015_0747_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0720_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 720 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 720 18 18, g32p_row24_traceSegment_015_0720_0018, g32p_row24_traceSegment_015_0738_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0756_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 756 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0765_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 765 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0756_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 756 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 756 9 9, g32p_row24_traceSegment_015_0756_0009, g32p_row24_traceSegment_015_0765_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0774_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 774 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0783_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 783 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0774_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 774 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 774 9 9, g32p_row24_traceSegment_015_0774_0009, g32p_row24_traceSegment_015_0783_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0756_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 756 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 756 18 18, g32p_row24_traceSegment_015_0756_0018, g32p_row24_traceSegment_015_0774_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0720_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 720 72 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 720 36 36, g32p_row24_traceSegment_015_0720_0036, g32p_row24_traceSegment_015_0756_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0792_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 792 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0801_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 801 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0792_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 792 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 792 9 9, g32p_row24_traceSegment_015_0792_0009, g32p_row24_traceSegment_015_0801_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0810_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 810 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0819_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 819 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0810_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 810 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 810 9 9, g32p_row24_traceSegment_015_0810_0009, g32p_row24_traceSegment_015_0819_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0792_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 792 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 792 18 18, g32p_row24_traceSegment_015_0792_0018, g32p_row24_traceSegment_015_0810_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0828_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 828 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0837_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 837 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0828_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 828 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 828 9 9, g32p_row24_traceSegment_015_0828_0009, g32p_row24_traceSegment_015_0837_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0846_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 846 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0855_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 855 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0846_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 846 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 846 9 9, g32p_row24_traceSegment_015_0846_0009, g32p_row24_traceSegment_015_0855_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0828_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 828 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 828 18 18, g32p_row24_traceSegment_015_0828_0018, g32p_row24_traceSegment_015_0846_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0792_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 792 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 792 36 36, g32p_row24_traceSegment_015_0792_0036, g32p_row24_traceSegment_015_0828_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0720_0144 : g32p_coeffSegment g32p_row24_traceSegment_015 720 144 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 720 72 72, g32p_row24_traceSegment_015_0720_0072, g32p_row24_traceSegment_015_0792_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0576_0288 : g32p_coeffSegment g32p_row24_traceSegment_015 576 288 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 576 144 144, g32p_row24_traceSegment_015_0576_0144, g32p_row24_traceSegment_015_0720_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0864_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 864 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0873_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 873 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0864_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 864 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 864 9 9, g32p_row24_traceSegment_015_0864_0009, g32p_row24_traceSegment_015_0873_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0882_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 882 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0891_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 891 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0882_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 882 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 882 9 9, g32p_row24_traceSegment_015_0882_0009, g32p_row24_traceSegment_015_0891_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0864_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 864 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 864 18 18, g32p_row24_traceSegment_015_0864_0018, g32p_row24_traceSegment_015_0882_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0900_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 900 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0909_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 909 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0900_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 900 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 900 9 9, g32p_row24_traceSegment_015_0900_0009, g32p_row24_traceSegment_015_0909_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0918_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 918 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0927_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 927 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0918_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 918 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 918 9 9, g32p_row24_traceSegment_015_0918_0009, g32p_row24_traceSegment_015_0927_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0900_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 900 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 900 18 18, g32p_row24_traceSegment_015_0900_0018, g32p_row24_traceSegment_015_0918_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0864_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 864 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 864 36 36, g32p_row24_traceSegment_015_0864_0036, g32p_row24_traceSegment_015_0900_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0936_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 936 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0945_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 945 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0936_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 936 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 936 9 9, g32p_row24_traceSegment_015_0936_0009, g32p_row24_traceSegment_015_0945_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0954_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 954 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0963_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 963 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0954_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 954 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 954 9 9, g32p_row24_traceSegment_015_0954_0009, g32p_row24_traceSegment_015_0963_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0936_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 936 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 936 18 18, g32p_row24_traceSegment_015_0936_0018, g32p_row24_traceSegment_015_0954_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0972_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 972 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0981_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 981 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0972_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 972 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 972 9 9, g32p_row24_traceSegment_015_0972_0009, g32p_row24_traceSegment_015_0981_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0990_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 990 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0999_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 999 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_0990_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 990 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 990 9 9, g32p_row24_traceSegment_015_0990_0009, g32p_row24_traceSegment_015_0999_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0972_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 972 36 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 972 18 18, g32p_row24_traceSegment_015_0972_0018, g32p_row24_traceSegment_015_0990_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0936_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 936 72 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 936 36 36, g32p_row24_traceSegment_015_0936_0036, g32p_row24_traceSegment_015_0972_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0864_0144 : g32p_coeffSegment g32p_row24_traceSegment_015 864 144 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 864 72 72, g32p_row24_traceSegment_015_0864_0072, g32p_row24_traceSegment_015_0936_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1008_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1008 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1017_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1017 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1008_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 1008 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1008 9 9, g32p_row24_traceSegment_015_1008_0009, g32p_row24_traceSegment_015_1017_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1026_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1026 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1035_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1035 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1026_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 1026 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1026 9 9, g32p_row24_traceSegment_015_1026_0009, g32p_row24_traceSegment_015_1035_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1008_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 1008 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1008 18 18, g32p_row24_traceSegment_015_1008_0018, g32p_row24_traceSegment_015_1026_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1044_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1044 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1053_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1053 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1044_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 1044 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1044 9 9, g32p_row24_traceSegment_015_1044_0009, g32p_row24_traceSegment_015_1053_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1062_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1062 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1071_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1071 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1062_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 1062 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1062 9 9, g32p_row24_traceSegment_015_1062_0009, g32p_row24_traceSegment_015_1071_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1044_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 1044 36 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1044 18 18, g32p_row24_traceSegment_015_1044_0018, g32p_row24_traceSegment_015_1062_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1008_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 1008 72 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1008 36 36, g32p_row24_traceSegment_015_1008_0036, g32p_row24_traceSegment_015_1044_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1080_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1080 9 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1089_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1089 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1080_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 1080 18 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1080 9 9, g32p_row24_traceSegment_015_1080_0009, g32p_row24_traceSegment_015_1089_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1098_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1098 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1107_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1107 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1098_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 1098 18 = [] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1098 9 9, g32p_row24_traceSegment_015_1098_0009, g32p_row24_traceSegment_015_1107_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1080_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 1080 36 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1080 18 18, g32p_row24_traceSegment_015_1080_0018, g32p_row24_traceSegment_015_1098_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1116_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1116 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1125_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1125 9 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1116_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 1116 18 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1116 9 9, g32p_row24_traceSegment_015_1116_0009, g32p_row24_traceSegment_015_1125_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1134_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1134 9 = [] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1143_0009 : g32p_coeffSegment g32p_row24_traceSegment_015 1143 9 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row24_traceSegment_015_1134_0018 : g32p_coeffSegment g32p_row24_traceSegment_015 1134 18 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1134 9 9, g32p_row24_traceSegment_015_1134_0009, g32p_row24_traceSegment_015_1143_0009]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1116_0036 : g32p_coeffSegment g32p_row24_traceSegment_015 1116 36 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1116 18 18, g32p_row24_traceSegment_015_1116_0018, g32p_row24_traceSegment_015_1134_0018]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1080_0072 : g32p_coeffSegment g32p_row24_traceSegment_015 1080 72 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1080 36 36, g32p_row24_traceSegment_015_1080_0036, g32p_row24_traceSegment_015_1116_0036]
  decide +kernel

private theorem g32p_row24_traceSegment_015_1008_0144 : g32p_coeffSegment g32p_row24_traceSegment_015 1008 144 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 1008 72 72, g32p_row24_traceSegment_015_1008_0072, g32p_row24_traceSegment_015_1080_0072]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0864_0288 : g32p_coeffSegment g32p_row24_traceSegment_015 864 288 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 864 144 144, g32p_row24_traceSegment_015_0864_0144, g32p_row24_traceSegment_015_1008_0144]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0576_0576 : g32p_coeffSegment g32p_row24_traceSegment_015 576 576 = [0, 0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 576 288 288, g32p_row24_traceSegment_015_0576_0288, g32p_row24_traceSegment_015_0864_0288]
  decide +kernel

private theorem g32p_row24_traceSegment_015_0000_1152 : g32p_coeffSegment g32p_row24_traceSegment_015 0 1152 = [0, 0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row24_traceSegment_015 0 576 576, g32p_row24_traceSegment_015_0000_0576, g32p_row24_traceSegment_015_0576_0576]
  decide +kernel

theorem g32p_row24_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row24_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row24_characterValues j)).val) 15 = [0, 0, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row24_traceSegment_015_0000_1152

end HodgeLean.Foundations.Program

end
end
