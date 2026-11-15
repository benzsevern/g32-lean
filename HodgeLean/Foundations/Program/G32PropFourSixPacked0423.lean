import HodgeLean.Foundations.Program.G32PropFourSixPacked0422
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow40
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

theorem g32p_row39_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row39_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row39_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row39_variantArithmetic_00_0 r
  · exact g32p_row39_variantArithmetic_01_0 r
  · exact g32p_row39_variantArithmetic_02_0 r
  · exact g32p_row39_variantArithmetic_03_0 r
  · exact g32p_row39_variantArithmetic_04_0 r
  · exact g32p_row39_variantArithmetic_05_0 r
  · exact g32p_row39_variantArithmetic_06_0 r

theorem g32p_row39_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row39_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row39_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row39_variantArithmetic_00_1 r
  · exact g32p_row39_variantArithmetic_01_1 r
  · exact g32p_row39_variantArithmetic_02_1 r
  · exact g32p_row39_variantArithmetic_03_1 r
  · exact g32p_row39_variantArithmetic_04_1 r
  · exact g32p_row39_variantArithmetic_05_1 r
  · exact g32p_row39_variantArithmetic_06_1 r

theorem g32p_row39_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row39_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row39_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row39_variantArithmetic_00_2 r
  · exact g32p_row39_variantArithmetic_01_2 r
  · exact g32p_row39_variantArithmetic_02_2 r
  · exact g32p_row39_variantArithmetic_03_2 r
  · exact g32p_row39_variantArithmetic_04_2 r
  · exact g32p_row39_variantArithmetic_05_2 r
  · exact g32p_row39_variantArithmetic_06_2 r

theorem g32p_row39_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row39_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row39_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row39_variantArithmetic_00_3 r
  · exact g32p_row39_variantArithmetic_01_3 r
  · exact g32p_row39_variantArithmetic_02_3 r
  · exact g32p_row39_variantArithmetic_03_3 r
  · exact g32p_row39_variantArithmetic_04_3 r
  · exact g32p_row39_variantArithmetic_05_3 r
  · exact g32p_row39_variantArithmetic_06_3 r

theorem g32p_row39_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row39_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row39_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row39_variantArithmetic_00_4 r
  · exact g32p_row39_variantArithmetic_01_4 r
  · exact g32p_row39_variantArithmetic_02_4 r
  · exact g32p_row39_variantArithmetic_03_4 r
  · exact g32p_row39_variantArithmetic_04_4 r
  · exact g32p_row39_variantArithmetic_05_4 r
  · exact g32p_row39_variantArithmetic_06_4 r

theorem g32p_row39_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row39_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row39_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row39_variantArithmetic_00_5 r
  · exact g32p_row39_variantArithmetic_01_5 r
  · exact g32p_row39_variantArithmetic_02_5 r
  · exact g32p_row39_variantArithmetic_03_5 r
  · exact g32p_row39_variantArithmetic_04_5 r
  · exact g32p_row39_variantArithmetic_05_5 r
  · exact g32p_row39_variantArithmetic_06_5 r

theorem g32p_row39_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row39_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row39_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row39_variantArithmetic_00_6 r
  · exact g32p_row39_variantArithmetic_01_6 r
  · exact g32p_row39_variantArithmetic_02_6 r
  · exact g32p_row39_variantArithmetic_03_6 r
  · exact g32p_row39_variantArithmetic_04_6 r
  · exact g32p_row39_variantArithmetic_05_6 r
  · exact g32p_row39_variantArithmetic_06_6 r

theorem g32p_row39_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row39_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row39_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 38 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row39_variantArithmetic_00_7 r
  · exact g32p_row39_variantArithmetic_01_7 r
  · exact g32p_row39_variantArithmetic_02_7 r
  · exact g32p_row39_variantArithmetic_03_7 r
  · exact g32p_row39_variantArithmetic_04_7 r
  · exact g32p_row39_variantArithmetic_05_7 r
  · exact g32p_row39_variantArithmetic_06_7 r

theorem g32p_row39_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row39_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row39_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 38 c _ (g32p_row39_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row39_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 38 c _ (g32p_row39_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row39_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 38 c _ (g32p_row39_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row39_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 38 c _ (g32p_row39_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row39_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 38 c _ (g32p_row39_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row39_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 38 c _ (g32p_row39_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row39_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 38 c _ (g32p_row39_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row39_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 38 c _ (g32p_row39_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row39_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup29_source : Fin 144 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (85, 24)) else (if i.val < 3 then (57, 102) else (30, 187))) else (if i.val < 6 then (if i.val < 5 then (30, 50) else (10, 83)) else (if i.val < 7 then (25, 127) else (if i.val < 8 then (14, 196) else (104, 121))))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then (28, 170) else (116, 114)) else (if i.val < 12 then (80, 106) else (10, 188))) else (if i.val < 15 then (if i.val < 14 then (14, 92) else (54, 124)) else (if i.val < 16 then (80, 162) else (if i.val < 17 then (139, 230) else (108, 233)))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then (7, 53) else (6, 197)) else (if i.val < 21 then (107, 240) else (10, 104))) else (if i.val < 24 then (if i.val < 23 then (29, 240) else (86, 74)) else (if i.val < 25 then (0, 99) else (if i.val < 26 then (142, 61) else (72, 165))))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then (73, 61) else (113, 138)) else (if i.val < 30 then (122, 249) else (133, 164))) else (if i.val < 33 then (if i.val < 32 then (38, 183) else (142, 172)) else (if i.val < 34 then (11, 232) else (if i.val < 35 then (134, 33) else (79, 37))))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then (78, 149) else (134, 55)) else (if i.val < 39 then (139, 151) else (63, 38))) else (if i.val < 42 then (if i.val < 41 then (80, 95) else (100, 213)) else (if i.val < 43 then (77, 90) else (if i.val < 44 then (16, 50) else (109, 158))))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then (52, 226) else (6, 150)) else (if i.val < 48 then (42, 58) else (33, 13))) else (if i.val < 51 then (if i.val < 50 then (108, 93) else (2, 195)) else (if i.val < 52 then (43, 83) else (if i.val < 53 then (88, 169) else (19, 118)))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then (125, 211) else (16, 11)) else (if i.val < 57 then (33, 14) else (31, 230))) else (if i.val < 60 then (if i.val < 59 then (32, 155) else (116, 98)) else (if i.val < 61 then (57, 232) else (if i.val < 62 then (5, 73) else (133, 63))))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then (93, 157) else (10, 87)) else (if i.val < 66 then (33, 146) else (57, 161))) else (if i.val < 69 then (if i.val < 68 then (54, 139) else (57, 187)) else (if i.val < 70 then (132, 186) else (if i.val < 71 then (47, 194) else (24, 69)))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then (87, 218) else (44, 239)) else (if i.val < 75 then (113, 231) else (5, 254))) else (if i.val < 78 then (if i.val < 77 then (113, 164) else (11, 114)) else (if i.val < 79 then (114, 206) else (if i.val < 80 then (15, 154) else (114, 122))))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then (115, 126) else (6, 73)) else (if i.val < 84 then (62, 239) else (25, 141))) else (if i.val < 87 then (if i.val < 86 then (8, 51) else (90, 7)) else (if i.val < 88 then (56, 57) else (if i.val < 89 then (102, 48) else (125, 189)))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then (85, 244) else (85, 143)) else (if i.val < 93 then (62, 224) else (125, 81))) else (if i.val < 96 then (if i.val < 95 then (62, 201) else (106, 181)) else (if i.val < 97 then (47, 219) else (if i.val < 98 then (142, 199) else (14, 210))))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then (8, 138) else (56, 132)) else (if i.val < 102 then (5, 113) else (102, 87))) else (if i.val < 105 then (if i.val < 104 then (5, 102) else (1, 155)) else (if i.val < 106 then (30, 73) else (if i.val < 107 then (90, 162) else (5, 143))))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then (29, 185) else (96, 36)) else (if i.val < 111 then (127, 250) else (5, 129))) else (if i.val < 114 then (if i.val < 113 then (138, 175) else (100, 226)) else (if i.val < 115 then (26, 6) else (if i.val < 116 then (121, 111) else (71, 3))))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then (74, 9) else (100, 218)) else (if i.val < 120 then (87, 114) else (122, 7))) else (if i.val < 123 then (if i.val < 122 then (113, 129) else (70, 147)) else (if i.val < 124 then (7, 174) else (if i.val < 125 then (102, 58) else (115, 86)))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then (105, 162) else (105, 107)) else (if i.val < 129 then (37, 46) else (131, 74))) else (if i.val < 132 then (if i.val < 131 then (125, 160) else (32, 142)) else (if i.val < 133 then (111, 75) else (if i.val < 134 then (139, 173) else (60, 180))))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then (14, 51) else (4, 144)) else (if i.val < 138 then (123, 82) else (31, 80))) else (if i.val < 141 then (if i.val < 140 then (132, 114) else (84, 206)) else (if i.val < 142 then (59, 225) else (if i.val < 143 then (102, 52) else (132, 230)))))))))

def g32p_supplierGroup29_classify : Fin 144 → Fin 102 :=
  fun i => (if i.val < 72 then (if i.val < 36 then (if i.val < 18 then (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 92) else (if i.val < 3 then 5 else 94)) else (if i.val < 6 then (if i.val < 5 then 76 else 18) else (if i.val < 7 then 11 else (if i.val < 8 then 92 else 29)))) else (if i.val < 13 then (if i.val < 11 then (if i.val < 10 then 93 else 29) else (if i.val < 12 then 92 else 18)) else (if i.val < 15 then (if i.val < 14 then 94 else 77) else (if i.val < 16 then 94 else (if i.val < 17 then 29 else 94))))) else (if i.val < 27 then (if i.val < 22 then (if i.val < 20 then (if i.val < 19 then 44 else 5) else (if i.val < 21 then 77 else 44)) else (if i.val < 24 then (if i.val < 23 then 67 else 19) else (if i.val < 25 then 99 else (if i.val < 26 then 25 else 56)))) else (if i.val < 31 then (if i.val < 29 then (if i.val < 28 then 45 else 25) else (if i.val < 30 then 25 else 29)) else (if i.val < 33 then (if i.val < 32 then 4 else 63) else (if i.val < 34 then 56 else (if i.val < 35 then 29 else 58)))))) else (if i.val < 54 then (if i.val < 45 then (if i.val < 40 then (if i.val < 38 then (if i.val < 37 then 92 else 63) else (if i.val < 39 then 58 else 32)) else (if i.val < 42 then (if i.val < 41 then 89 else 25) else (if i.val < 43 then 29 else (if i.val < 44 then 5 else 94)))) else (if i.val < 49 then (if i.val < 47 then (if i.val < 46 then 77 else 4) else (if i.val < 48 then 19 else 5)) else (if i.val < 51 then (if i.val < 50 then 77 else 44) else (if i.val < 52 then 67 else (if i.val < 53 then 56 else 4))))) else (if i.val < 63 then (if i.val < 58 then (if i.val < 56 then (if i.val < 55 then 29 else 44) else (if i.val < 57 then 5 else 19)) else (if i.val < 60 then (if i.val < 59 then 23 else 63) else (if i.val < 61 then 19 else (if i.val < 62 then 67 else 58)))) else (if i.val < 67 then (if i.val < 65 then (if i.val < 64 then 23 else 67) else (if i.val < 66 then 23 else 23)) else (if i.val < 69 then (if i.val < 68 then 94 else 5) else (if i.val < 70 then 25 else (if i.val < 71 then 25 else 45))))))) else (if i.val < 108 then (if i.val < 90 then (if i.val < 81 then (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 10 else 45) else (if i.val < 75 then 10 else 1)) else (if i.val < 78 then (if i.val < 77 then 10 else 11) else (if i.val < 79 then 29 else (if i.val < 80 then 3 else 25)))) else (if i.val < 85 then (if i.val < 83 then (if i.val < 82 then 58 else 2) else (if i.val < 84 then 15 else 56)) else (if i.val < 87 then (if i.val < 86 then 11 else 58) else (if i.val < 88 then 35 else (if i.val < 89 then 45 else 58))))) else (if i.val < 99 then (if i.val < 94 then (if i.val < 92 then (if i.val < 91 then 15 else 10) else (if i.val < 93 then 35 else 15)) else (if i.val < 96 then (if i.val < 95 then 35 else 66) else (if i.val < 97 then 11 else (if i.val < 98 then 63 else 76)))) else (if i.val < 103 then (if i.val < 101 then (if i.val < 100 then 4 else 76) else (if i.val < 102 then 79 else 25)) else (if i.val < 105 then (if i.val < 104 then 95 else 95) else (if i.val < 106 then 79 else (if i.val < 107 then 63 else 76)))))) else (if i.val < 126 then (if i.val < 117 then (if i.val < 112 then (if i.val < 110 then (if i.val < 109 then 95 else 79) else (if i.val < 111 then 63 else 95)) else (if i.val < 114 then (if i.val < 113 then 86 else 84) else (if i.val < 115 then 84 else (if i.val < 116 then 48 else 84)))) else (if i.val < 121 then (if i.val < 119 then (if i.val < 118 then 80 else 84) else (if i.val < 120 then 48 else 80)) else (if i.val < 123 then (if i.val < 122 then 48 else 80) else (if i.val < 124 then 8 else (if i.val < 125 then 86 else 15))))) else (if i.val < 135 then (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then 66 else 35) else (if i.val < 129 then 32 else 86)) else (if i.val < 132 then (if i.val < 131 then 66 else 32) else (if i.val < 133 then 86 else (if i.val < 134 then 66 else 32)))) else (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then 79 else 81) else (if i.val < 138 then 80 else 98)) else (if i.val < 141 then (if i.val < 140 then 48 else 80) else (if i.val < 142 then 48 else (if i.val < 143 then 80 else 48))))))))

def g32p_supplierGroup29_support : Finset (Fin 102) :=
  {0, 1, 2, 3, 4, 5, 8, 10, 11, 15, 18, 19, 23, 25, 29, 32, 35, 44, 45, 48, 56, 58, 63, 66, 67, 76, 77, 79, 80, 81, 84, 86, 89, 92, 93, 94, 95, 98, 99}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup29_matrix_000 : ∀ r : Fin 16,
    g32p_row40_groupNodes (g32p_finBlockIndex 144 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 0 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup29_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 0 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 0 r)).2 =
      g32p_supplierGroup29_classify (g32p_finBlockIndex 144 0 r) := by
  decide +kernel

theorem g32p_supplierGroup29_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup29_classify (g32p_finBlockIndex 144 0 r) ∈ g32p_supplierGroup29_support := by
  decide +kernel

theorem g32p_supplierGroup29_matrix_001 : ∀ r : Fin 16,
    g32p_row40_groupNodes (g32p_finBlockIndex 144 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 1 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup29_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 1 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 1 r)).2 =
      g32p_supplierGroup29_classify (g32p_finBlockIndex 144 1 r) := by
  decide +kernel

theorem g32p_supplierGroup29_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup29_classify (g32p_finBlockIndex 144 1 r) ∈ g32p_supplierGroup29_support := by
  decide +kernel

theorem g32p_supplierGroup29_matrix_002 : ∀ r : Fin 16,
    g32p_row40_groupNodes (g32p_finBlockIndex 144 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 2 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup29_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 2 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 2 r)).2 =
      g32p_supplierGroup29_classify (g32p_finBlockIndex 144 2 r) := by
  decide +kernel

theorem g32p_supplierGroup29_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup29_classify (g32p_finBlockIndex 144 2 r) ∈ g32p_supplierGroup29_support := by
  decide +kernel

theorem g32p_supplierGroup29_matrix_003 : ∀ r : Fin 16,
    g32p_row40_groupNodes (g32p_finBlockIndex 144 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 3 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup29_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 3 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 3 r)).2 =
      g32p_supplierGroup29_classify (g32p_finBlockIndex 144 3 r) := by
  decide +kernel

theorem g32p_supplierGroup29_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup29_classify (g32p_finBlockIndex 144 3 r) ∈ g32p_supplierGroup29_support := by
  decide +kernel

theorem g32p_supplierGroup29_matrix_004 : ∀ r : Fin 16,
    g32p_row40_groupNodes (g32p_finBlockIndex 144 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 4 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup29_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 4 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 4 r)).2 =
      g32p_supplierGroup29_classify (g32p_finBlockIndex 144 4 r) := by
  decide +kernel

theorem g32p_supplierGroup29_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup29_classify (g32p_finBlockIndex 144 4 r) ∈ g32p_supplierGroup29_support := by
  decide +kernel

theorem g32p_supplierGroup29_matrix_005 : ∀ r : Fin 16,
    g32p_row40_groupNodes (g32p_finBlockIndex 144 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 5 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup29_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 5 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 5 r)).2 =
      g32p_supplierGroup29_classify (g32p_finBlockIndex 144 5 r) := by
  decide +kernel

theorem g32p_supplierGroup29_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup29_classify (g32p_finBlockIndex 144 5 r) ∈ g32p_supplierGroup29_support := by
  decide +kernel

theorem g32p_supplierGroup29_matrix_006 : ∀ r : Fin 16,
    g32p_row40_groupNodes (g32p_finBlockIndex 144 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 6 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup29_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 6 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 6 r)).2 =
      g32p_supplierGroup29_classify (g32p_finBlockIndex 144 6 r) := by
  decide +kernel

theorem g32p_supplierGroup29_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup29_classify (g32p_finBlockIndex 144 6 r) ∈ g32p_supplierGroup29_support := by
  decide +kernel

theorem g32p_supplierGroup29_matrix_007 : ∀ r : Fin 16,
    g32p_row40_groupNodes (g32p_finBlockIndex 144 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 7 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup29_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 7 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 7 r)).2 =
      g32p_supplierGroup29_classify (g32p_finBlockIndex 144 7 r) := by
  decide +kernel

theorem g32p_supplierGroup29_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup29_classify (g32p_finBlockIndex 144 7 r) ∈ g32p_supplierGroup29_support := by
  decide +kernel

theorem g32p_supplierGroup29_matrix_008 : ∀ r : Fin 16,
    g32p_row40_groupNodes (g32p_finBlockIndex 144 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 8 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup29_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup29_source (g32p_finBlockIndex 144 8 r)).1 (g32p_supplierGroup29_source (g32p_finBlockIndex 144 8 r)).2 =
      g32p_supplierGroup29_classify (g32p_finBlockIndex 144 8 r) := by
  decide +kernel

theorem g32p_supplierGroup29_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup29_classify (g32p_finBlockIndex 144 8 r) ∈ g32p_supplierGroup29_support := by
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

theorem g32p_supplierGroup29_matrix (i : Fin 144) :
    g32p_row40_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source i).1 (g32p_supplierGroup29_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row40_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup29_source i).1 (g32p_supplierGroup29_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup29_matrix_000 r
  · exact g32p_supplierGroup29_matrix_001 r
  · exact g32p_supplierGroup29_matrix_002 r
  · exact g32p_supplierGroup29_matrix_003 r
  · exact g32p_supplierGroup29_matrix_004 r
  · exact g32p_supplierGroup29_matrix_005 r
  · exact g32p_supplierGroup29_matrix_006 r
  · exact g32p_supplierGroup29_matrix_007 r
  · exact g32p_supplierGroup29_matrix_008 r

theorem g32p_supplierGroup29_class (i : Fin 144) :
    g32p_supplierForest_classes (g32p_supplierGroup29_source i).1 (g32p_supplierGroup29_source i).2 =
      g32p_supplierGroup29_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup29_source i).1 (g32p_supplierGroup29_source i).2 =
      g32p_supplierGroup29_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup29_class_000 r
  · exact g32p_supplierGroup29_class_001 r
  · exact g32p_supplierGroup29_class_002 r
  · exact g32p_supplierGroup29_class_003 r
  · exact g32p_supplierGroup29_class_004 r
  · exact g32p_supplierGroup29_class_005 r
  · exact g32p_supplierGroup29_class_006 r
  · exact g32p_supplierGroup29_class_007 r
  · exact g32p_supplierGroup29_class_008 r

theorem g32p_supplierGroup29_support_mem (i : Fin 144) :
    g32p_supplierGroup29_classify i ∈ g32p_supplierGroup29_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup29_classify i ∈ g32p_supplierGroup29_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup29_support_000 r
  · exact g32p_supplierGroup29_support_001 r
  · exact g32p_supplierGroup29_support_002 r
  · exact g32p_supplierGroup29_support_003 r
  · exact g32p_supplierGroup29_support_004 r
  · exact g32p_supplierGroup29_support_005 r
  · exact g32p_supplierGroup29_support_006 r
  · exact g32p_supplierGroup29_support_007 r
  · exact g32p_supplierGroup29_support_008 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row40_supplierClassifier : Fin 144 → Fin 102 := g32p_supplierGroup29_classify

theorem g32p_row40_groupEquiv_isConj (i : Fin 144) :
    IsConj (g32p_row40_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row40_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup29_source i).1 (g32p_supplierGroup29_source i).2
  rw [g32p_supplierGroup29_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row40_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup29_matrix i)

def g32p_row40_supplierClass (h : (g32p_recordedSuppliers 39).H) : Fin 102 :=
  g32p_row40_supplierClassifier (g32p_row40_groupEquiv.symm h)

theorem g32p_row40_supplierClass_isConj (h : (g32p_recordedSuppliers 39).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row40_supplierClass h)) := by
  have he : (g32p_row40_groupEquiv (g32p_row40_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 39).H => (a : g32p_G))
      (g32p_row40_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row40_supplierClassifier (g32p_row40_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row40_groupEquiv_isConj (g32p_row40_groupEquiv.symm h)

theorem g32p_row40_supplierClass_iff (h : (g32p_recordedSuppliers 39).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row40_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row40_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row40_supplierClass_isConj h).symm

theorem g32p_row40_supplierClass_mem_support (h : (g32p_recordedSuppliers 39).H) :
    g32p_row40_supplierClass h ∈ g32p_supplierGroup29_support :=
  g32p_supplierGroup29_support_mem (g32p_row40_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row40_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 0) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 0) (g32p_literalTraceValue 39 0)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_000]
  decide +kernel

theorem g32p_row40_traceCoefficients_001 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 1 = [0, 1] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 1) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 1) (g32p_literalTraceValue 39 1)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_001]
  decide +kernel

theorem g32p_row40_traceCoefficients_002 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 2 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 2) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 2) (g32p_literalTraceValue 39 2)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row40_traceCoefficients_002]
  decide +kernel

theorem g32p_row40_traceCoefficients_003 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 3 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 3) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 3) (g32p_literalTraceValue 39 3)
      [1, 1, 1] [432] = true := by
  rw [g32p_row40_traceCoefficients_003]
  decide +kernel

theorem g32p_row40_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 4 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 4) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 4) (g32p_literalTraceValue 39 4)
      [1, 1, 1] [2592] = true := by
  rw [g32p_row40_traceCoefficients_004]
  decide +kernel

theorem g32p_row40_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 5 = [6] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 5) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 5) (g32p_literalTraceValue 39 5)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_005]
  decide +kernel

theorem g32p_row40_traceCoefficients_008 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 8 = [0, 1] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_008 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 8) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 8) (g32p_literalTraceValue 39 8)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_008]
  decide +kernel

theorem g32p_row40_traceCoefficients_010 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 10 = [0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_010 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 10) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 10) (g32p_literalTraceValue 39 10)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_010]
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

theorem g32p_row40_traceCoefficients_011 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 11 = [0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_011 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 11) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 11) (g32p_literalTraceValue 39 11)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_011]
  decide +kernel

theorem g32p_row40_traceCoefficients_015 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 15 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_015 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 15) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 15) (g32p_literalTraceValue 39 15)
      [1, 1, 1] [432] = true := by
  rw [g32p_row40_traceCoefficients_015]
  decide +kernel

theorem g32p_row40_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 18 = [2] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 18) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 18) (g32p_literalTraceValue 39 18)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_018]
  decide +kernel

theorem g32p_row40_traceCoefficients_019 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 19 = [4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_019 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 19) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 19) (g32p_literalTraceValue 39 19)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_019]
  decide +kernel

theorem g32p_row40_traceCoefficients_023 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 23 = [4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_023 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 23) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 23) (g32p_literalTraceValue 39 23)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_023]
  decide +kernel

theorem g32p_row40_traceCoefficients_025 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 25 = [0, 8] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_025 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 25) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 25) (g32p_literalTraceValue 39 25)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_025]
  decide +kernel

theorem g32p_row40_traceCoefficients_029 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 29 = [0, 0, 8] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_029 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 29) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 29) (g32p_literalTraceValue 39 29)
      [1, 1, 1] [864] = true := by
  rw [g32p_row40_traceCoefficients_029]
  decide +kernel

theorem g32p_row40_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 32 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 32) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 32) (g32p_literalTraceValue 39 32)
      [1, 1, 1] [1296] = true := by
  rw [g32p_row40_traceCoefficients_032]
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

theorem g32p_row40_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 35 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 35) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 35) (g32p_literalTraceValue 39 35)
      [1, 1, 1] [1296] = true := by
  rw [g32p_row40_traceCoefficients_035]
  decide +kernel

theorem g32p_row40_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 44 = [4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 44) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 44) (g32p_literalTraceValue 39 44)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_044]
  decide +kernel

theorem g32p_row40_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 45 = [0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 45) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 45) (g32p_literalTraceValue 39 45)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_045]
  decide +kernel

theorem g32p_row40_traceCoefficients_048 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 48 = [0, 6] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_048 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 48) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 48) (g32p_literalTraceValue 39 48)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_048]
  decide +kernel

theorem g32p_row40_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 56 = [0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 56) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 56) (g32p_literalTraceValue 39 56)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_056]
  decide +kernel

theorem g32p_row40_traceCoefficients_058 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 58 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_058 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 58) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 58) (g32p_literalTraceValue 39 58)
      [1, 1, 1] [432] = true := by
  rw [g32p_row40_traceCoefficients_058]
  decide +kernel

theorem g32p_row40_traceCoefficients_063 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 63 = [0, 0, 6] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_063 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 63) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 63) (g32p_literalTraceValue 39 63)
      [1, 1, 1] [432] = true := by
  rw [g32p_row40_traceCoefficients_063]
  decide +kernel

theorem g32p_row40_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 66 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 66) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 66) (g32p_literalTraceValue 39 66)
      [1, 1, 1] [432] = true := by
  rw [g32p_row40_traceCoefficients_066]
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

theorem g32p_row40_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 67 = [4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 67) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 67) (g32p_literalTraceValue 39 67)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_067]
  decide +kernel

theorem g32p_row40_traceCoefficients_076 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 76 = [4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 76) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 76) (g32p_literalTraceValue 39 76)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_076]
  decide +kernel

theorem g32p_row40_traceCoefficients_077 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 77 = [4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 77) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 77) (g32p_literalTraceValue 39 77)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_077]
  decide +kernel

theorem g32p_row40_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 79 = [4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 79) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 79) (g32p_literalTraceValue 39 79)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_079]
  decide +kernel

theorem g32p_row40_traceCoefficients_080 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 80 = [0, 6] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_080 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 80) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 80) (g32p_literalTraceValue 39 80)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_080]
  decide +kernel

theorem g32p_row40_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 81 = [0, 1] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 81) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 81) (g32p_literalTraceValue 39 81)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_081]
  decide +kernel

theorem g32p_row40_traceCoefficients_084 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 84 = [0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 84) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 84) (g32p_literalTraceValue 39 84)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_084]
  decide +kernel

theorem g32p_row40_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 86 = [0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 86) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 86) (g32p_literalTraceValue 39 86)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_086]
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

theorem g32p_row40_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 89 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 89) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 89) (g32p_literalTraceValue 39 89)
      [1, 1, 1] [432] = true := by
  rw [g32p_row40_traceCoefficients_089]
  decide +kernel

theorem g32p_row40_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 92 = [0, 0, 4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 92) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 92) (g32p_literalTraceValue 39 92)
      [1, 1, 1] [2592] = true := by
  rw [g32p_row40_traceCoefficients_092]
  decide +kernel

theorem g32p_row40_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 93 = [0, 0, 1] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 93) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 93) (g32p_literalTraceValue 39 93)
      [1, 1, 1] [3888] = true := by
  rw [g32p_row40_traceCoefficients_093]
  decide +kernel

theorem g32p_row40_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 94 = [6] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 94) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 94) (g32p_literalTraceValue 39 94)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_094]
  decide +kernel

theorem g32p_row40_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 95 = [4] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 95) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 95) (g32p_literalTraceValue 39 95)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_095]
  decide +kernel

theorem g32p_row40_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 98 = [0, 1] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_098 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 98) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 98) (g32p_literalTraceValue 39 98)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_098]
  decide +kernel

theorem g32p_row40_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 99 = [1] := by
  decide +kernel

theorem g32p_row40_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer 99) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) 99) (g32p_literalTraceValue 39 99)
      [1, 1, 1] [] = true := by
  rw [g32p_row40_traceCoefficients_099]
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

def g32p_row40_generatorIndex : Fin 8 → Fin 408 :=
  ![39, 90, 141, 192, 282, 283, 384, 385]

theorem g32p_row40_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup29_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 39 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 39 g32p_row40_supplierClass
    g32p_row40_supplierClass_isConj g32p_supplierGroup29_support g32p_row40_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row40_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup29_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row40_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 39 c false (g32p_row40_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 39 c true (g32p_row40_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 39 c false (g32p_row40_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 39 c true (g32p_row40_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 39 c false (g32p_row40_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 39 c false (g32p_row40_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 39 c true (g32p_row40_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 39 c true (g32p_row40_coinduced_zero c hc true) 3

theorem g32p_row40_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup29_support →
      g32p_literalTraceValue (g32p_row40_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row40_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup29_support →
      g32p_literalTraceValue (g32p_row40_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row40_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup29_support →
      g32p_literalTraceValue (g32p_row40_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row40_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup29_support →
      g32p_literalTraceValue (g32p_row40_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row40_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup29_support →
      g32p_literalTraceValue (g32p_row40_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row40_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup29_support →
      g32p_literalTraceValue (g32p_row40_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row40_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup29_support →
      g32p_literalTraceValue (g32p_row40_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row40_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup29_support) :
    g32p_literalTraceValue (g32p_row40_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup29_support →
    g32p_literalTraceValue (g32p_row40_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row40_zeroTrace_block_00 r k
  · exact g32p_row40_zeroTrace_block_01 r k
  · exact g32p_row40_zeroTrace_block_02 r k
  · exact g32p_row40_zeroTrace_block_03 r k
  · exact g32p_row40_zeroTrace_block_04 r k
  · exact g32p_row40_zeroTrace_block_05 r k
  · exact g32p_row40_zeroTrace_block_06 r k

theorem g32p_row40_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup29_support) :
    (g32p_recordedInductionGenerators (g32p_row40_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row40_generatorIndex k) c) := by
  rw [g32p_row40_recordedGenerator_zero c hc k, g32p_row40_zeroTrace_arithmetic c k hc]
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

def g32p_row40_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [3888])) else (if i.val < 4 then [432] else (if i.val < 5 then [2592] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [432] else (if i.val < 17 then [] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else []) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [864] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [1296] else [])) else (if i.val < 36 then (if i.val < 35 then [] else [1296]) else (if i.val < 37 then [] else [])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [432] else [])) else (if i.val < 61 then [] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [432] else (if i.val < 65 then [] else [])) else (if i.val < 67 then [432] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else []) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [432] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [2592] else (if i.val < 94 then [3888] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [])))))))

theorem g32p_row40_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup29_support) :
    g32p_supplierTracePolynomialCheck 144 (g32p_literalCentralizer c) 3
      (g32p_supplierTraceCoefficients g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) c) (g32p_literalTraceValue 39 c)
      [1, 1, 1] (g32p_row40_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row40_tracePolynomial_000
  · exact g32p_row40_tracePolynomial_001
  · exact g32p_row40_tracePolynomial_002
  · exact g32p_row40_tracePolynomial_003
  · exact g32p_row40_tracePolynomial_004
  · exact g32p_row40_tracePolynomial_005
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_008
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_010
  · exact g32p_row40_tracePolynomial_011
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (13 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_015
  · exact False.elim ((by decide : (16 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_018
  · exact g32p_row40_tracePolynomial_019
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (22 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_023
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_025
  · exact False.elim ((by decide : (26 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_029
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_032
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (34 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_035
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (37 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_044
  · exact g32p_row40_tracePolynomial_045
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (47 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_048
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_056
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_058
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (60 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_063
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (65 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_066
  · exact g32p_row40_tracePolynomial_067
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (69 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (73 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_076
  · exact g32p_row40_tracePolynomial_077
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_079
  · exact g32p_row40_tracePolynomial_080
  · exact g32p_row40_tracePolynomial_081
  · exact False.elim ((by decide : (82 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_084
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_086
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_089
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_092
  · exact g32p_row40_tracePolynomial_093
  · exact g32p_row40_tracePolynomial_094
  · exact g32p_row40_tracePolynomial_095
  · exact False.elim ((by decide : (96 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (97 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact g32p_row40_tracePolynomial_098
  · exact g32p_row40_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup29_support) hc)
  · exact False.elim ((by decide : (101 : Fin 102) ∉ g32p_supplierGroup29_support) hc)

theorem g32p_row40_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 39 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 39 c) := by
  by_cases hc : c ∈ g32p_supplierGroup29_support
  · have hclass (j : Fin 144) :
        IsConj (g32p_literalRepresentative c) (g32p_row40_groupEquiv j : g32p_G) ↔
          g32p_row40_supplierClassifier j = c := by
      simpa only [g32p_row40_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row40_supplierClass_iff (g32p_row40_groupEquiv j) c
    have hχ (j : Fin 144) :
        (g32p_recordedSupplierCharacters 39 (g32p_row40_groupEquiv j) : ℂ) =
          g32p_root 3 ^ (Multiplicative.toAdd (g32p_row40_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 39 (show (g32p_recordedSuppliers 39).H from g32p_row40_groupEquiv j)]
      change g32p_root 3 ^ (Multiplicative.toAdd
        (g32p_row40_characterValues (g32p_row40_groupEquiv.symm (g32p_row40_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 39).H (g32p_recordedSupplierCharacters 39)
      (g32p_literalRepresentative c) g32p_row40_groupEquiv g32p_row40_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row40_characterValues j)).val) c 3 144
      (g32p_literalCentralizer c) (g32p_literalTraceValue 39 c) [1, 1, 1]
      (g32p_row40_traceQuotient c) (g32p_root 3) (by decide)
      g32p_row40_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_three
        (g32p_root_primitive (g32p_recordedSuppliers 39)))
      (g32p_row40_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 3 (by decide)] at h
    exact h
  · exact g32p_row40_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row40_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
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

theorem g32p_row40_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
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

theorem g32p_row40_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
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

theorem g32p_row40_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row40_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row40_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 39 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
