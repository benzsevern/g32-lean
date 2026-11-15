import HodgeLean.Foundations.Program.G32PropFourSixPacked0345
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow06
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row05_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row05_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row05_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row05_variantArithmetic_00_0 r
  · exact g32p_row05_variantArithmetic_01_0 r
  · exact g32p_row05_variantArithmetic_02_0 r
  · exact g32p_row05_variantArithmetic_03_0 r
  · exact g32p_row05_variantArithmetic_04_0 r
  · exact g32p_row05_variantArithmetic_05_0 r
  · exact g32p_row05_variantArithmetic_06_0 r

theorem g32p_row05_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row05_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row05_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row05_variantArithmetic_00_1 r
  · exact g32p_row05_variantArithmetic_01_1 r
  · exact g32p_row05_variantArithmetic_02_1 r
  · exact g32p_row05_variantArithmetic_03_1 r
  · exact g32p_row05_variantArithmetic_04_1 r
  · exact g32p_row05_variantArithmetic_05_1 r
  · exact g32p_row05_variantArithmetic_06_1 r

theorem g32p_row05_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row05_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row05_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row05_variantArithmetic_00_2 r
  · exact g32p_row05_variantArithmetic_01_2 r
  · exact g32p_row05_variantArithmetic_02_2 r
  · exact g32p_row05_variantArithmetic_03_2 r
  · exact g32p_row05_variantArithmetic_04_2 r
  · exact g32p_row05_variantArithmetic_05_2 r
  · exact g32p_row05_variantArithmetic_06_2 r

theorem g32p_row05_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row05_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row05_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row05_variantArithmetic_00_3 r
  · exact g32p_row05_variantArithmetic_01_3 r
  · exact g32p_row05_variantArithmetic_02_3 r
  · exact g32p_row05_variantArithmetic_03_3 r
  · exact g32p_row05_variantArithmetic_04_3 r
  · exact g32p_row05_variantArithmetic_05_3 r
  · exact g32p_row05_variantArithmetic_06_3 r

theorem g32p_row05_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row05_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row05_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row05_variantArithmetic_00_4 r
  · exact g32p_row05_variantArithmetic_01_4 r
  · exact g32p_row05_variantArithmetic_02_4 r
  · exact g32p_row05_variantArithmetic_03_4 r
  · exact g32p_row05_variantArithmetic_04_4 r
  · exact g32p_row05_variantArithmetic_05_4 r
  · exact g32p_row05_variantArithmetic_06_4 r

theorem g32p_row05_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row05_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row05_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row05_variantArithmetic_00_5 r
  · exact g32p_row05_variantArithmetic_01_5 r
  · exact g32p_row05_variantArithmetic_02_5 r
  · exact g32p_row05_variantArithmetic_03_5 r
  · exact g32p_row05_variantArithmetic_04_5 r
  · exact g32p_row05_variantArithmetic_05_5 r
  · exact g32p_row05_variantArithmetic_06_5 r

theorem g32p_row05_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row05_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row05_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row05_variantArithmetic_00_6 r
  · exact g32p_row05_variantArithmetic_01_6 r
  · exact g32p_row05_variantArithmetic_02_6 r
  · exact g32p_row05_variantArithmetic_03_6 r
  · exact g32p_row05_variantArithmetic_04_6 r
  · exact g32p_row05_variantArithmetic_05_6 r
  · exact g32p_row05_variantArithmetic_06_6 r

theorem g32p_row05_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row05_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row05_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 4 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row05_variantArithmetic_00_7 r
  · exact g32p_row05_variantArithmetic_01_7 r
  · exact g32p_row05_variantArithmetic_02_7 r
  · exact g32p_row05_variantArithmetic_03_7 r
  · exact g32p_row05_variantArithmetic_04_7 r
  · exact g32p_row05_variantArithmetic_05_7 r
  · exact g32p_row05_variantArithmetic_06_7 r

theorem g32p_row05_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row05_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row05_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 4 c _ (g32p_row05_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row05_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 4 c _ (g32p_row05_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row05_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 4 c _ (g32p_row05_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row05_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 4 c _ (g32p_row05_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row05_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 4 c _ (g32p_row05_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row05_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 4 c _ (g32p_row05_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row05_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 4 c _ (g32p_row05_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row05_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 4 c _ (g32p_row05_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row05_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup04_source : Fin 144 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (21, 117)) else (if i.val < 3 then (57, 102) else (30, 187))) else (if i.val < 6 then (if i.val < 5 then (30, 50) else (10, 83)) else (if i.val < 7 then (30, 117) else (if i.val < 8 then (39, 113) else (120, 159))))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then (30, 40) else (95, 141)) else (if i.val < 12 then (33, 111) else (10, 188))) else (if i.val < 15 then (if i.val < 14 then (14, 92) else (54, 124)) else (if i.val < 16 then (80, 162) else (if i.val < 17 then (119, 240) else (108, 233)))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then (7, 53) else (6, 197)) else (if i.val < 21 then (107, 240) else (10, 104))) else (if i.val < 24 then (if i.val < 23 then (29, 240) else (86, 74)) else (if i.val < 25 then (0, 99) else (if i.val < 26 then (81, 100) else (57, 122))))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then (23, 12) else (95, 18)) else (if i.val < 30 then (118, 77) else (93, 17))) else (if i.val < 33 then (if i.val < 32 then (14, 97) else (129, 178)) else (if i.val < 34 then (10, 36) else (if i.val < 35 then (93, 114) else (92, 159))))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then (5, 240) else (66, 165)) else (if i.val < 39 then (128, 104) else (120, 17))) else (if i.val < 42 then (if i.val < 41 then (86, 197) else (66, 143)) else (if i.val < 43 then (42, 127) else (if i.val < 44 then (16, 50) else (109, 158))))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then (52, 226) else (22, 243)) else (if i.val < 48 then (42, 58) else (33, 13))) else (if i.val < 51 then (if i.val < 50 then (108, 93) else (2, 195)) else (if i.val < 52 then (43, 83) else (if i.val < 53 then (15, 5) else (29, 153)))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then (42, 156) else (16, 11)) else (if i.val < 57 then (33, 14) else (31, 230))) else (if i.val < 60 then (if i.val < 59 then (32, 155) else (93, 230)) else (if i.val < 61 then (57, 232) else (if i.val < 62 then (5, 73) else (132, 52))))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then (93, 157) else (10, 87)) else (if i.val < 66 then (33, 146) else (57, 161))) else (if i.val < 69 then (if i.val < 68 then (54, 139) else (57, 187)) else (if i.val < 70 then (65, 204) else (if i.val < 71 then (95, 87) else (86, 66)))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then (128, 193) else (93, 58)) else (if i.val < 75 then (140, 184) else (109, 218))) else (if i.val < 78 then (if i.val < 77 then (108, 14) else (56, 123)) else (if i.val < 79 then (68, 29) else (if i.val < 80 then (53, 94) else (67, 73))))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then (132, 76) else (107, 123)) else (if i.val < 84 then (118, 241) else (21, 99))) else (if i.val < 87 then (if i.val < 86 then (11, 51) else (142, 0)) else (if i.val < 88 then (6, 195) else (if i.val < 89 then (15, 227) else (120, 4)))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then (136, 40) else (130, 89)) else (if i.val < 93 then (86, 92) else (132, 46))) else (if i.val < 96 then (if i.val < 95 then (68, 246) else (30, 42)) else (if i.val < 97 then (54, 207) else (if i.val < 98 then (109, 62) else (14, 210))))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then (82, 125) else (56, 132)) else (if i.val < 102 then (5, 113) else (119, 82))) else (if i.val < 105 then (if i.val < 104 then (5, 102) else (1, 155)) else (if i.val < 106 then (30, 73) else (if i.val < 107 then (136, 67) else (5, 143))))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then (29, 185) else (96, 36)) else (if i.val < 111 then (66, 104) else (5, 129))) else (if i.val < 114 then (if i.val < 113 then (112, 145) else (39, 201)) else (if i.val < 115 then (67, 29) else (if i.val < 116 then (118, 245) else (22, 125))))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then (119, 233) else (107, 198)) else (if i.val < 120 then (135, 162) else (135, 94))) else (if i.val < 123 then (if i.val < 122 then (143, 73) else (118, 113)) else (if i.val < 124 then (54, 174) else (if i.val < 125 then (96, 51) else (86, 141)))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then (40, 255) else (39, 159)) else (if i.val < 129 then (95, 226) else (86, 202))) else (if i.val < 132 then (if i.val < 131 then (29, 178) else (120, 31)) else (if i.val < 133 then (65, 85) else (if i.val < 134 then (53, 252) else (129, 232))))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then (14, 51) else (57, 159)) else (if i.val < 138 then (96, 11) else (6, 234))) else (if i.val < 141 then (if i.val < 140 then (120, 3) else (130, 70)) else (if i.val < 142 then (143, 62) else (if i.val < 143 then (120, 165) else (92, 88)))))))))

def g32p_supplierGroup04_classify : Fin 144 → Fin 102 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 24) else (if i.val < 3 then 5 else 94)) else (if i.val < 6 then (if i.val < 5 then 76 else 18) else (if i.val < 7 then 78 else (if i.val < 8 then 24 else 43)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 95 else 43) else (if i.val < 12 then 24 else 18)) else (if i.val < 15 then (if i.val < 14 then 94 else 77) else (if i.val < 16 then 94 else (if i.val < 17 then 43 else 94))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then 44 else 5) else (if i.val < 21 then 77 else 44)) else (if i.val < 24 then (if i.val < 23 then 67 else 19) else (if i.val < 25 then 99 else (if i.val < 26 then 74 else 24)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then 6 else 74) else (if i.val < 30 then 74 else 43)) else (if i.val < 33 then (if i.val < 32 then 78 else 72) else (if i.val < 34 then 24 else (if i.val < 35 then 43 else 7)))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then 24 else 72) else (if i.val < 39 then 7 else 75)) else (if i.val < 42 then (if i.val < 41 then 23 else 74) else (if i.val < 43 then 43 else (if i.val < 44 then 5 else 94)))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then 77 else 78) else (if i.val < 48 then 19 else 5)) else (if i.val < 51 then (if i.val < 50 then 77 else 44) else (if i.val < 52 then 67 else (if i.val < 53 then 24 else 78))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then 43 else 44) else (if i.val < 57 then 5 else 19)) else (if i.val < 60 then (if i.val < 59 then 23 else 72) else (if i.val < 61 then 19 else (if i.val < 62 then 67 else 7)))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then 23 else 67) else (if i.val < 66 then 23 else 23)) else (if i.val < 69 then (if i.val < 68 then 94 else 5) else (if i.val < 70 then 74 else (if i.val < 71 then 74 else 6))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 71 else 6) else (if i.val < 75 then 71 else 76)) else (if i.val < 78 then (if i.val < 77 then 71 else 78) else (if i.val < 79 then 43 else (if i.val < 80 then 79 else 74)))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then 7 else 67) else (if i.val < 84 then 40 else 24)) else (if i.val < 87 then (if i.val < 86 then 78 else 7) else (if i.val < 88 then 6 else (if i.val < 89 then 6 else 7))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then 40 else 71) else (if i.val < 93 then 6 else 40)) else (if i.val < 96 then (if i.val < 95 then 6 else 71) else (if i.val < 97 then 78 else (if i.val < 98 then 72 else 76)))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then 78 else 76) else (if i.val < 102 then 79 else 74)) else (if i.val < 105 then (if i.val < 104 then 95 else 95) else (if i.val < 106 then 79 else (if i.val < 107 then 72 else 76)))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 95 else 79) else (if i.val < 111 then 72 else 95)) else (if i.val < 114 then (if i.val < 113 then 40 else 75) else (if i.val < 115 then 75 else (if i.val < 116 then 20 else 75)))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 41 else 75) else (if i.val < 120 then 20 else 41)) else (if i.val < 123 then (if i.val < 122 then 20 else 41) else (if i.val < 124 then 77 else (if i.val < 125 then 40 else 40))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then 71 else 6) else (if i.val < 129 then 75 else 40)) else (if i.val < 132 then (if i.val < 131 then 71 else 75) else (if i.val < 133 then 40 else (if i.val < 134 then 71 else 75)))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then 79 else 19) else (if i.val < 138 then 41 else 44)) else (if i.val < 141 then (if i.val < 140 then 20 else 41) else (if i.val < 142 then 20 else (if i.val < 143 then 41 else 20))))))))

def g32p_supplierGroup04_support : Finset (Fin 102) :=
  {0, 5, 6, 7, 18, 19, 20, 23, 24, 40, 41, 43, 44, 67, 71, 72, 74, 75, 76, 77, 78, 79, 94, 95, 99}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup04_matrix_000 : ∀ r : Fin 16,
    g32p_row06_groupNodes (g32p_finBlockIndex 144 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 0 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup04_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 0 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 0 r)).2 =
      g32p_supplierGroup04_classify (g32p_finBlockIndex 144 0 r) := by
  decide +kernel

theorem g32p_supplierGroup04_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup04_classify (g32p_finBlockIndex 144 0 r) ∈ g32p_supplierGroup04_support := by
  decide +kernel

theorem g32p_supplierGroup04_matrix_001 : ∀ r : Fin 16,
    g32p_row06_groupNodes (g32p_finBlockIndex 144 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 1 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup04_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 1 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 1 r)).2 =
      g32p_supplierGroup04_classify (g32p_finBlockIndex 144 1 r) := by
  decide +kernel

theorem g32p_supplierGroup04_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup04_classify (g32p_finBlockIndex 144 1 r) ∈ g32p_supplierGroup04_support := by
  decide +kernel

theorem g32p_supplierGroup04_matrix_002 : ∀ r : Fin 16,
    g32p_row06_groupNodes (g32p_finBlockIndex 144 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 2 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup04_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 2 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 2 r)).2 =
      g32p_supplierGroup04_classify (g32p_finBlockIndex 144 2 r) := by
  decide +kernel

theorem g32p_supplierGroup04_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup04_classify (g32p_finBlockIndex 144 2 r) ∈ g32p_supplierGroup04_support := by
  decide +kernel

theorem g32p_supplierGroup04_matrix_003 : ∀ r : Fin 16,
    g32p_row06_groupNodes (g32p_finBlockIndex 144 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 3 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup04_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 3 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 3 r)).2 =
      g32p_supplierGroup04_classify (g32p_finBlockIndex 144 3 r) := by
  decide +kernel

theorem g32p_supplierGroup04_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup04_classify (g32p_finBlockIndex 144 3 r) ∈ g32p_supplierGroup04_support := by
  decide +kernel

theorem g32p_supplierGroup04_matrix_004 : ∀ r : Fin 16,
    g32p_row06_groupNodes (g32p_finBlockIndex 144 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 4 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup04_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 4 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 4 r)).2 =
      g32p_supplierGroup04_classify (g32p_finBlockIndex 144 4 r) := by
  decide +kernel

theorem g32p_supplierGroup04_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup04_classify (g32p_finBlockIndex 144 4 r) ∈ g32p_supplierGroup04_support := by
  decide +kernel

theorem g32p_supplierGroup04_matrix_005 : ∀ r : Fin 16,
    g32p_row06_groupNodes (g32p_finBlockIndex 144 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 5 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup04_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 5 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 5 r)).2 =
      g32p_supplierGroup04_classify (g32p_finBlockIndex 144 5 r) := by
  decide +kernel

theorem g32p_supplierGroup04_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup04_classify (g32p_finBlockIndex 144 5 r) ∈ g32p_supplierGroup04_support := by
  decide +kernel

theorem g32p_supplierGroup04_matrix_006 : ∀ r : Fin 16,
    g32p_row06_groupNodes (g32p_finBlockIndex 144 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 6 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup04_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 6 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 6 r)).2 =
      g32p_supplierGroup04_classify (g32p_finBlockIndex 144 6 r) := by
  decide +kernel

theorem g32p_supplierGroup04_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup04_classify (g32p_finBlockIndex 144 6 r) ∈ g32p_supplierGroup04_support := by
  decide +kernel

theorem g32p_supplierGroup04_matrix_007 : ∀ r : Fin 16,
    g32p_row06_groupNodes (g32p_finBlockIndex 144 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 7 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup04_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 7 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 7 r)).2 =
      g32p_supplierGroup04_classify (g32p_finBlockIndex 144 7 r) := by
  decide +kernel

theorem g32p_supplierGroup04_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup04_classify (g32p_finBlockIndex 144 7 r) ∈ g32p_supplierGroup04_support := by
  decide +kernel

theorem g32p_supplierGroup04_matrix_008 : ∀ r : Fin 16,
    g32p_row06_groupNodes (g32p_finBlockIndex 144 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 8 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup04_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup04_source (g32p_finBlockIndex 144 8 r)).1 (g32p_supplierGroup04_source (g32p_finBlockIndex 144 8 r)).2 =
      g32p_supplierGroup04_classify (g32p_finBlockIndex 144 8 r) := by
  decide +kernel

theorem g32p_supplierGroup04_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup04_classify (g32p_finBlockIndex 144 8 r) ∈ g32p_supplierGroup04_support := by
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

theorem g32p_supplierGroup04_matrix (i : Fin 144) :
    g32p_row06_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source i).1 (g32p_supplierGroup04_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row06_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup04_source i).1 (g32p_supplierGroup04_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup04_matrix_000 r
  · exact g32p_supplierGroup04_matrix_001 r
  · exact g32p_supplierGroup04_matrix_002 r
  · exact g32p_supplierGroup04_matrix_003 r
  · exact g32p_supplierGroup04_matrix_004 r
  · exact g32p_supplierGroup04_matrix_005 r
  · exact g32p_supplierGroup04_matrix_006 r
  · exact g32p_supplierGroup04_matrix_007 r
  · exact g32p_supplierGroup04_matrix_008 r

theorem g32p_supplierGroup04_class (i : Fin 144) :
    g32p_supplierForest_classes (g32p_supplierGroup04_source i).1 (g32p_supplierGroup04_source i).2 =
      g32p_supplierGroup04_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup04_source i).1 (g32p_supplierGroup04_source i).2 =
      g32p_supplierGroup04_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup04_class_000 r
  · exact g32p_supplierGroup04_class_001 r
  · exact g32p_supplierGroup04_class_002 r
  · exact g32p_supplierGroup04_class_003 r
  · exact g32p_supplierGroup04_class_004 r
  · exact g32p_supplierGroup04_class_005 r
  · exact g32p_supplierGroup04_class_006 r
  · exact g32p_supplierGroup04_class_007 r
  · exact g32p_supplierGroup04_class_008 r

theorem g32p_supplierGroup04_support_mem (i : Fin 144) :
    g32p_supplierGroup04_classify i ∈ g32p_supplierGroup04_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup04_classify i ∈ g32p_supplierGroup04_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup04_support_000 r
  · exact g32p_supplierGroup04_support_001 r
  · exact g32p_supplierGroup04_support_002 r
  · exact g32p_supplierGroup04_support_003 r
  · exact g32p_supplierGroup04_support_004 r
  · exact g32p_supplierGroup04_support_005 r
  · exact g32p_supplierGroup04_support_006 r
  · exact g32p_supplierGroup04_support_007 r
  · exact g32p_supplierGroup04_support_008 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row06_supplierClassifier : Fin 144 → Fin 102 := g32p_supplierGroup04_classify

theorem g32p_row06_groupEquiv_isConj (i : Fin 144) :
    IsConj (g32p_row06_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row06_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup04_source i).1 (g32p_supplierGroup04_source i).2
  rw [g32p_supplierGroup04_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row06_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup04_matrix i)

def g32p_row06_supplierClass (h : (g32p_recordedSuppliers 5).H) : Fin 102 :=
  g32p_row06_supplierClassifier (g32p_row06_groupEquiv.symm h)

theorem g32p_row06_supplierClass_isConj (h : (g32p_recordedSuppliers 5).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row06_supplierClass h)) := by
  have he : (g32p_row06_groupEquiv (g32p_row06_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 5).H => (a : g32p_G))
      (g32p_row06_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row06_supplierClassifier (g32p_row06_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row06_groupEquiv_isConj (g32p_row06_groupEquiv.symm h)

theorem g32p_row06_supplierClass_iff (h : (g32p_recordedSuppliers 5).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row06_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row06_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row06_supplierClass_isConj h).symm

theorem g32p_row06_supplierClass_mem_support (h : (g32p_recordedSuppliers 5).H) :
    g32p_row06_supplierClass h ∈ g32p_supplierGroup04_support :=
  g32p_supplierGroup04_support_mem (g32p_row06_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row06_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 0) (g32p_literalTraceValue 5 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row06_traceCoefficients_000]
  decide +kernel

theorem g32p_row06_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 5 = [6] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 5) (g32p_literalTraceValue 5 5)
      [1, -1, 1] [] = true := by
  rw [g32p_row06_traceCoefficients_005]
  decide +kernel

theorem g32p_row06_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 6 = [0, 0, 4, 0, 4] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 6) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 6) (g32p_literalTraceValue 5 6)
      [1, -1, 1] [1296, 1296, 1296] = true := by
  rw [g32p_row06_traceCoefficients_006]
  decide +kernel

theorem g32p_row06_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 7 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 7) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 7) (g32p_literalTraceValue 5 7)
      [1, -1, 1] [] = true := by
  rw [g32p_row06_traceCoefficients_007]
  decide +kernel

theorem g32p_row06_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 18 = [1, 0, 0, 1] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 18) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 18) (g32p_literalTraceValue 5 18)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row06_traceCoefficients_018]
  decide +kernel

theorem g32p_row06_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 19 = [0, 0, 0, 4, 1] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 19) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 19) (g32p_literalTraceValue 5 19)
      [1, -1, 1] [2160, 2160, 432] = true := by
  rw [g32p_row06_traceCoefficients_019]
  decide +kernel

theorem g32p_row06_traceCoefficients_020 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 20 = [0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_020 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 20) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 20) (g32p_literalTraceValue 5 20)
      [1, -1, 1] [432, 432, 432] = true := by
  rw [g32p_row06_traceCoefficients_020]
  decide +kernel

theorem g32p_row06_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 23 = [0, 0, 1, 4] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 23) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 23) (g32p_literalTraceValue 5 23)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row06_traceCoefficients_023]
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

theorem g32p_row06_traceCoefficients_024 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 24 = [0, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_024 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 24) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 24) (g32p_literalTraceValue 5 24)
      [1, -1, 1] [-2592, 0, 2592, 2592] = true := by
  rw [g32p_row06_traceCoefficients_024]
  decide +kernel

theorem g32p_row06_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 40 = [0, 0, 0, 0, 4, 4] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 40) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 40) (g32p_literalTraceValue 5 40)
      [1, -1, 1] [432, 432, 864, 432] = true := by
  rw [g32p_row06_traceCoefficients_040]
  decide +kernel

theorem g32p_row06_traceCoefficients_041 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 41 = [0, 6] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_041 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 41) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 41) (g32p_literalTraceValue 5 41)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row06_traceCoefficients_041]
  decide +kernel

theorem g32p_row06_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 43 = [0, 0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 43) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 43) (g32p_literalTraceValue 5 43)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row06_traceCoefficients_043]
  decide +kernel

theorem g32p_row06_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 44 = [0, 1, 0, 4] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 44) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 44) (g32p_literalTraceValue 5 44)
      [1, -1, 1] [11664, 15552] = true := by
  rw [g32p_row06_traceCoefficients_044]
  decide +kernel

theorem g32p_row06_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 67 = [4, 0, 1] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 67) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 67) (g32p_literalTraceValue 5 67)
      [1, -1, 1] [] = true := by
  rw [g32p_row06_traceCoefficients_067]
  decide +kernel

theorem g32p_row06_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 71 = [0, 4, 4] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_071 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 71) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 71) (g32p_literalTraceValue 5 71)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row06_traceCoefficients_071]
  decide +kernel

theorem g32p_row06_traceCoefficients_072 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 72 = [0, 0, 0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_072 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 72) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 72) (g32p_literalTraceValue 5 72)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row06_traceCoefficients_072]
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

theorem g32p_row06_traceCoefficients_074 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 74 = [0, 4, 0, 0, 4] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 74) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 74) (g32p_literalTraceValue 5 74)
      [1, -1, 1] [0, 432, 432] = true := by
  rw [g32p_row06_traceCoefficients_074]
  decide +kernel

theorem g32p_row06_traceCoefficients_075 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 75 = [0, 4, 0, 0, 0, 4] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 75) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 75) (g32p_literalTraceValue 5 75)
      [1, -1, 1] [-1296, 0, 1296, 1296] = true := by
  rw [g32p_row06_traceCoefficients_075]
  decide +kernel

theorem g32p_row06_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 76 = [4, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 76) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 76) (g32p_literalTraceValue 5 76)
      [1, -1, 1] [3888, 3888, 3888] = true := by
  rw [g32p_row06_traceCoefficients_076]
  decide +kernel

theorem g32p_row06_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 77 = [4, 1] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 77) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 77) (g32p_literalTraceValue 5 77)
      [1, -1, 1] [-432] = true := by
  rw [g32p_row06_traceCoefficients_077]
  decide +kernel

theorem g32p_row06_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 78 = [0, 0, 4, 0, 4] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 78) (g32p_literalTraceValue 5 78)
      [1, -1, 1] [2592, 2592, 2592] = true := by
  rw [g32p_row06_traceCoefficients_078]
  decide +kernel

theorem g32p_row06_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 79 = [4, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 79) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 79) (g32p_literalTraceValue 5 79)
      [1, -1, 1] [0, 0, 432, 432] = true := by
  rw [g32p_row06_traceCoefficients_079]
  decide +kernel

theorem g32p_row06_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 94 = [0, 0, 0, 6] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 94) (g32p_literalTraceValue 5 94)
      [1, -1, 1] [1728, 1728] = true := by
  rw [g32p_row06_traceCoefficients_094]
  decide +kernel

theorem g32p_row06_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 95 = [0, 0, 0, 4, 0, 1] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 95) (g32p_literalTraceValue 5 95)
      [1, -1, 1] [15552, 15552, 3888, 3888] = true := by
  rw [g32p_row06_traceCoefficients_095]
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

theorem g32p_row06_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 99 = [0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row06_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 99) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) 99) (g32p_literalTraceValue 5 99)
      [1, -1, 1] [155520, 155520] = true := by
  rw [g32p_row06_traceCoefficients_099]
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

def g32p_row06_generatorIndex : Fin 8 → Fin 408 :=
  ![5, 56, 107, 158, 214, 215, 316, 317]

theorem g32p_row06_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup04_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 5 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 5 g32p_row06_supplierClass
    g32p_row06_supplierClass_isConj g32p_supplierGroup04_support g32p_row06_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row06_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup04_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row06_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 5 c false (g32p_row06_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 5 c true (g32p_row06_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 5 c false (g32p_row06_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 5 c true (g32p_row06_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 5 c false (g32p_row06_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 5 c false (g32p_row06_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 5 c true (g32p_row06_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 5 c true (g32p_row06_coinduced_zero c hc true) 3

theorem g32p_row06_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup04_support →
      g32p_literalTraceValue (g32p_row06_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row06_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup04_support →
      g32p_literalTraceValue (g32p_row06_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row06_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup04_support →
      g32p_literalTraceValue (g32p_row06_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row06_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup04_support →
      g32p_literalTraceValue (g32p_row06_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row06_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup04_support →
      g32p_literalTraceValue (g32p_row06_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row06_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup04_support →
      g32p_literalTraceValue (g32p_row06_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row06_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup04_support →
      g32p_literalTraceValue (g32p_row06_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row06_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup04_support) :
    g32p_literalTraceValue (g32p_row06_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup04_support →
    g32p_literalTraceValue (g32p_row06_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row06_zeroTrace_block_00 r k
  · exact g32p_row06_zeroTrace_block_01 r k
  · exact g32p_row06_zeroTrace_block_02 r k
  · exact g32p_row06_zeroTrace_block_03 r k
  · exact g32p_row06_zeroTrace_block_04 r k
  · exact g32p_row06_zeroTrace_block_05 r k
  · exact g32p_row06_zeroTrace_block_06 r k

theorem g32p_row06_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup04_support) :
    (g32p_recordedInductionGenerators (g32p_row06_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row06_generatorIndex k) c) := by
  rw [g32p_row06_recordedGenerator_zero c hc k, g32p_row06_zeroTrace_arithmetic c k hc]
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

def g32p_row06_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [1296, 1296, 1296] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [1728, 1728] else (if i.val < 20 then [2160, 2160, 432] else [432, 432, 432])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [1728, 1728] else [-2592, 0, 2592, 2592]))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [] else []) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [432, 432, 864, 432])) else (if i.val < 42 then [-432] else (if i.val < 43 then [] else [0, 0, 432, 432]))) else (if i.val < 47 then (if i.val < 45 then [11664, 15552] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [-432])) else (if i.val < 74 then (if i.val < 73 then [0, 0, 432, 432] else []) else (if i.val < 75 then [0, 432, 432] else [-1296, 0, 1296, 1296]))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [3888, 3888, 3888] else (if i.val < 78 then [-432] else [2592, 2592, 2592])) else (if i.val < 80 then [0, 0, 432, 432] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else [1728, 1728]))) else (if i.val < 98 then (if i.val < 96 then [15552, 15552, 3888, 3888] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else [155520, 155520]) else (if i.val < 101 then [] else [])))))))

theorem g32p_row06_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup04_support) :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer c) 6
      (g32p_supplierTraceCoefficients g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) c) (g32p_literalTraceValue 5 c)
      [1, -1, 1] (g32p_row06_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row06_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact g32p_row06_tracePolynomial_005
  · exact g32p_row06_tracePolynomial_006
  · exact g32p_row06_tracePolynomial_007
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact g32p_row06_tracePolynomial_018
  · exact g32p_row06_tracePolynomial_019
  · exact g32p_row06_tracePolynomial_020
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact g32p_row06_tracePolynomial_023
  · exact g32p_row06_tracePolynomial_024
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact g32p_row06_tracePolynomial_040
  · exact g32p_row06_tracePolynomial_041
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact g32p_row06_tracePolynomial_043
  · exact g32p_row06_tracePolynomial_044
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact g32p_row06_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact g32p_row06_tracePolynomial_071
  · exact g32p_row06_tracePolynomial_072
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact g32p_row06_tracePolynomial_074
  · exact g32p_row06_tracePolynomial_075
  · exact g32p_row06_tracePolynomial_076
  · exact g32p_row06_tracePolynomial_077
  · exact g32p_row06_tracePolynomial_078
  · exact g32p_row06_tracePolynomial_079
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact g32p_row06_tracePolynomial_094
  · exact g32p_row06_tracePolynomial_095
  · exact False.elim ((by decide : (96 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact g32p_row06_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup04_support) hc)
  · exact False.elim ((by decide : (101 : Fin 102) ∉ g32p_supplierGroup04_support) hc)

theorem g32p_row06_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 5 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 5 c) := by
  by_cases hc : c ∈ g32p_supplierGroup04_support
  · have hclass (j : Fin 144) :
        IsConj (g32p_literalRepresentative c) (g32p_row06_groupEquiv j : g32p_G) ↔
          g32p_row06_supplierClassifier j = c := by
      simpa only [g32p_row06_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row06_supplierClass_iff (g32p_row06_groupEquiv j) c
    have hχ (j : Fin 144) :
        (g32p_recordedSupplierCharacters 5 (g32p_row06_groupEquiv j) : ℂ) =
          g32p_root 6 ^ (Multiplicative.toAdd (g32p_row06_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 5 (show (g32p_recordedSuppliers 5).H from g32p_row06_groupEquiv j)]
      change g32p_root 6 ^ (Multiplicative.toAdd
        (g32p_row06_characterValues (g32p_row06_groupEquiv.symm (g32p_row06_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 5).H (g32p_recordedSupplierCharacters 5)
      (g32p_literalRepresentative c) g32p_row06_groupEquiv g32p_row06_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row06_characterValues j)).val) c 6 144
      (g32p_literalCentralizer c) (g32p_literalTraceValue 5 c) [1, -1, 1]
      (g32p_row06_traceQuotient c) (g32p_root 6) (by decide)
      g32p_row06_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_six
        (g32p_root_primitive (g32p_recordedSuppliers 5)))
      (g32p_row06_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 6 (by decide)] at h
    exact h
  · exact g32p_row06_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row06_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
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

theorem g32p_row06_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
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

theorem g32p_row06_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
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

theorem g32p_row06_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
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

theorem g32p_row06_variantArithmetic_04_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_04_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_04_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_04_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_04_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_04_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_04_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row06_variantArithmetic_04_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 4 r
    g32p_literalTraceValue (g32p_row06_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 5 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
