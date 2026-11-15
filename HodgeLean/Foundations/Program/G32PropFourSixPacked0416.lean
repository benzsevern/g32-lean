import HodgeLean.Foundations.Program.G32PropFourSixPacked0415
import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow34
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPairingRoots
import HodgeLean.Foundations.Program.G32PropFourSixPacked0207

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row33_variantArithmetic_06_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row33_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row33_variantArithmetic_06_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row33_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row33_variantArithmetic_06_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row33_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row33_variantArithmetic_06_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row33_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row33_variantArithmetic_06_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row33_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row33_variantArithmetic_06_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row33_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row33_variantArithmetic_06_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row33_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row33_variantArithmetic_06_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 6 r
    g32p_literalTraceValue (g32p_row33_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
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

theorem g32p_row33_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row33_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row33_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row33_variantArithmetic_00_0 r
  · exact g32p_row33_variantArithmetic_01_0 r
  · exact g32p_row33_variantArithmetic_02_0 r
  · exact g32p_row33_variantArithmetic_03_0 r
  · exact g32p_row33_variantArithmetic_04_0 r
  · exact g32p_row33_variantArithmetic_05_0 r
  · exact g32p_row33_variantArithmetic_06_0 r

theorem g32p_row33_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row33_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row33_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row33_variantArithmetic_00_1 r
  · exact g32p_row33_variantArithmetic_01_1 r
  · exact g32p_row33_variantArithmetic_02_1 r
  · exact g32p_row33_variantArithmetic_03_1 r
  · exact g32p_row33_variantArithmetic_04_1 r
  · exact g32p_row33_variantArithmetic_05_1 r
  · exact g32p_row33_variantArithmetic_06_1 r

theorem g32p_row33_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row33_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row33_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row33_variantArithmetic_00_2 r
  · exact g32p_row33_variantArithmetic_01_2 r
  · exact g32p_row33_variantArithmetic_02_2 r
  · exact g32p_row33_variantArithmetic_03_2 r
  · exact g32p_row33_variantArithmetic_04_2 r
  · exact g32p_row33_variantArithmetic_05_2 r
  · exact g32p_row33_variantArithmetic_06_2 r

theorem g32p_row33_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row33_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row33_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row33_variantArithmetic_00_3 r
  · exact g32p_row33_variantArithmetic_01_3 r
  · exact g32p_row33_variantArithmetic_02_3 r
  · exact g32p_row33_variantArithmetic_03_3 r
  · exact g32p_row33_variantArithmetic_04_3 r
  · exact g32p_row33_variantArithmetic_05_3 r
  · exact g32p_row33_variantArithmetic_06_3 r

theorem g32p_row33_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row33_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row33_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row33_variantArithmetic_00_4 r
  · exact g32p_row33_variantArithmetic_01_4 r
  · exact g32p_row33_variantArithmetic_02_4 r
  · exact g32p_row33_variantArithmetic_03_4 r
  · exact g32p_row33_variantArithmetic_04_4 r
  · exact g32p_row33_variantArithmetic_05_4 r
  · exact g32p_row33_variantArithmetic_06_4 r

theorem g32p_row33_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row33_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row33_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row33_variantArithmetic_00_5 r
  · exact g32p_row33_variantArithmetic_01_5 r
  · exact g32p_row33_variantArithmetic_02_5 r
  · exact g32p_row33_variantArithmetic_03_5 r
  · exact g32p_row33_variantArithmetic_04_5 r
  · exact g32p_row33_variantArithmetic_05_5 r
  · exact g32p_row33_variantArithmetic_06_5 r

theorem g32p_row33_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row33_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row33_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row33_variantArithmetic_00_6 r
  · exact g32p_row33_variantArithmetic_01_6 r
  · exact g32p_row33_variantArithmetic_02_6 r
  · exact g32p_row33_variantArithmetic_03_6 r
  · exact g32p_row33_variantArithmetic_04_6 r
  · exact g32p_row33_variantArithmetic_05_6 r
  · exact g32p_row33_variantArithmetic_06_6 r

theorem g32p_row33_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row33_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row33_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 32 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row33_variantArithmetic_00_7 r
  · exact g32p_row33_variantArithmetic_01_7 r
  · exact g32p_row33_variantArithmetic_02_7 r
  · exact g32p_row33_variantArithmetic_03_7 r
  · exact g32p_row33_variantArithmetic_04_7 r
  · exact g32p_row33_variantArithmetic_05_7 r
  · exact g32p_row33_variantArithmetic_06_7 r

theorem g32p_row33_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row33_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row33_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 32 c _ (g32p_row33_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row33_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 32 c _ (g32p_row33_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row33_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 32 c _ (g32p_row33_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row33_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 32 c _ (g32p_row33_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row33_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 32 c _ (g32p_row33_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row33_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 32 c _ (g32p_row33_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row33_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 32 c _ (g32p_row33_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row33_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 32 c _ (g32p_row33_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row33_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup25_source : Fin 480 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 240 then (if i.val < 120 then (if i.val < 60 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then (0, 0) else (if i.val < 2 then (137, 152) else (2, 178))) else (if i.val < 5 then (if i.val < 4 then (91, 84) else (121, 103)) else (if i.val < 6 then (132, 119) else (117, 200)))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then (105, 97) else (140, 94)) else (if i.val < 10 then (125, 79) else (73, 43))) else (if i.val < 13 then (if i.val < 12 then (142, 58) else (129, 138)) else (if i.val < 14 then (108, 16) else (82, 42))))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then (125, 140) else (if i.val < 17 then (118, 172) else (139, 253))) else (if i.val < 20 then (if i.val < 19 then (115, 243) else (0, 37)) else (if i.val < 21 then (87, 79) else (138, 180)))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then (110, 102) else (82, 90)) else (if i.val < 25 then (123, 87) else (118, 253))) else (if i.val < 28 then (if i.val < 27 then (135, 104) else (144, 180)) else (if i.val < 29 then (21, 239) else (140, 229)))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then (82, 80) else (if i.val < 32 then (116, 171) else (141, 30))) else (if i.val < 35 then (if i.val < 34 then (3, 158) else (28, 196)) else (if i.val < 36 then (37, 19) else (137, 161)))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then (50, 63) else (31, 68)) else (if i.val < 40 then (75, 31) else (1, 21))) else (if i.val < 43 then (if i.val < 42 then (99, 100) else (123, 12)) else (if i.val < 44 then (97, 208) else (107, 185))))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then (73, 85) else (if i.val < 47 then (100, 35) else (130, 167))) else (if i.val < 50 then (if i.val < 49 then (108, 125) else (59, 175)) else (if i.val < 51 then (130, 96) else (117, 70)))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then (130, 197) else (108, 75)) else (if i.val < 55 then (92, 198) else (129, 192))) else (if i.val < 58 then (if i.val < 57 then (77, 170) else (129, 156)) else (if i.val < 59 then (37, 180) else (18, 159))))))) else (if i.val < 90 then (if i.val < 75 then (if i.val < 67 then (if i.val < 63 then (if i.val < 61 then (140, 99) else (if i.val < 62 then (78, 139) else (36, 125))) else (if i.val < 65 then (if i.val < 64 then (26, 215) else (88, 17)) else (if i.val < 66 then (9, 98) else (60, 56)))) else (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then (36, 59) else (38, 187)) else (if i.val < 70 then (70, 19) else (19, 224))) else (if i.val < 73 then (if i.val < 72 then (63, 231) else (59, 240)) else (if i.val < 74 then (38, 46) else (121, 192))))) else (if i.val < 82 then (if i.val < 78 then (if i.val < 76 then (105, 125) else (if i.val < 77 then (17, 102) else (142, 32))) else (if i.val < 80 then (if i.val < 79 then (141, 63) else (114, 205)) else (if i.val < 81 then (136, 187) else (84, 173)))) else (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then (46, 218) else (107, 238)) else (if i.val < 85 then (143, 213) else (57, 152))) else (if i.val < 88 then (if i.val < 87 then (119, 238) else (102, 9)) else (if i.val < 89 then (108, 223) else (66, 113)))))) else (if i.val < 105 then (if i.val < 97 then (if i.val < 93 then (if i.val < 91 then (93, 191) else (if i.val < 92 then (79, 108) else (142, 6))) else (if i.val < 95 then (if i.val < 94 then (140, 197) else (128, 162)) else (if i.val < 96 then (96, 35) else (38, 169)))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then (117, 218) else (109, 187)) else (if i.val < 100 then (38, 199) else (132, 49))) else (if i.val < 103 then (if i.val < 102 then (120, 117) else (49, 244)) else (if i.val < 104 then (140, 162) else (19, 132))))) else (if i.val < 112 then (if i.val < 108 then (if i.val < 106 then (129, 124) else (if i.val < 107 then (49, 113) else (135, 42))) else (if i.val < 110 then (if i.val < 109 then (27, 231) else (114, 127)) else (if i.val < 111 then (28, 67) else (123, 55)))) else (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then (131, 250) else (79, 249)) else (if i.val < 115 then (140, 69) else (48, 171))) else (if i.val < 118 then (if i.val < 117 then (73, 167) else (134, 59)) else (if i.val < 119 then (130, 214) else (100, 210)))))))) else (if i.val < 180 then (if i.val < 150 then (if i.val < 135 then (if i.val < 127 then (if i.val < 123 then (if i.val < 121 then (125, 194) else (if i.val < 122 then (123, 220) else (122, 234))) else (if i.val < 125 then (if i.val < 124 then (110, 47) else (117, 150)) else (if i.val < 126 then (114, 88) else (70, 233)))) else (if i.val < 131 then (if i.val < 129 then (if i.val < 128 then (121, 36) else (133, 3)) else (if i.val < 130 then (121, 195) else (131, 168))) else (if i.val < 133 then (if i.val < 132 then (39, 206) else (143, 218)) else (if i.val < 134 then (130, 138) else (121, 222))))) else (if i.val < 142 then (if i.val < 138 then (if i.val < 136 then (144, 131) else (if i.val < 137 then (143, 249) else (117, 234))) else (if i.val < 140 then (if i.val < 139 then (137, 26) else (86, 186)) else (if i.val < 141 then (93, 40) else (100, 84)))) else (if i.val < 146 then (if i.val < 144 then (if i.val < 143 then (137, 134) else (144, 119)) else (if i.val < 145 then (132, 2) else (0, 96))) else (if i.val < 148 then (if i.val < 147 then (21, 178) else (135, 152)) else (if i.val < 149 then (112, 210) else (126, 144)))))) else (if i.val < 165 then (if i.val < 157 then (if i.val < 153 then (if i.val < 151 then (81, 66) else (if i.val < 152 then (125, 221) else (133, 120))) else (if i.val < 155 then (if i.val < 154 then (56, 174) else (141, 230)) else (if i.val < 156 then (106, 136) else (126, 179)))) else (if i.val < 161 then (if i.val < 159 then (if i.val < 158 then (132, 235) else (142, 122)) else (if i.val < 160 then (36, 194) else (139, 58))) else (if i.val < 163 then (if i.val < 162 then (144, 68) else (88, 251)) else (if i.val < 164 then (63, 227) else (127, 28))))) else (if i.val < 172 then (if i.val < 168 then (if i.val < 166 then (128, 19) else (if i.val < 167 then (20, 178) else (3, 0))) else (if i.val < 170 then (if i.val < 169 then (90, 79) else (73, 53)) else (if i.val < 171 then (144, 167) else (114, 111)))) else (if i.val < 176 then (if i.val < 174 then (if i.val < 173 then (113, 223) else (57, 18)) else (if i.val < 175 then (125, 24) else (46, 166))) else (if i.val < 178 then (if i.val < 177 then (140, 14) else (134, 166)) else (if i.val < 179 then (139, 196) else (11, 178))))))) else (if i.val < 210 then (if i.val < 195 then (if i.val < 187 then (if i.val < 183 then (if i.val < 181 then (46, 236) else (if i.val < 182 then (73, 20) else (92, 125))) else (if i.val < 185 then (if i.val < 184 then (12, 49) else (118, 69)) else (if i.val < 186 then (108, 135) else (4, 193)))) else (if i.val < 191 then (if i.val < 189 then (if i.val < 188 then (95, 95) else (134, 183)) else (if i.val < 190 then (92, 200) else (135, 117))) else (if i.val < 193 then (if i.val < 192 then (144, 144) else (134, 247)) else (if i.val < 194 then (96, 44) else (120, 99))))) else (if i.val < 202 then (if i.val < 198 then (if i.val < 196 then (129, 151) else (if i.val < 197 then (107, 191) else (119, 207))) else (if i.val < 200 then (if i.val < 199 then (117, 184) else (112, 48)) else (if i.val < 201 then (130, 15) else (38, 217)))) else (if i.val < 206 then (if i.val < 204 then (if i.val < 203 then (142, 3) else (90, 230)) else (if i.val < 205 then (139, 202) else (120, 184))) else (if i.val < 208 then (if i.val < 207 then (135, 156) else (142, 112)) else (if i.val < 209 then (32, 218) else (97, 151)))))) else (if i.val < 225 then (if i.val < 217 then (if i.val < 213 then (if i.val < 211 then (69, 59) else (if i.val < 212 then (128, 10) else (140, 34))) else (if i.val < 215 then (if i.val < 214 then (75, 215) else (73, 158)) else (if i.val < 216 then (128, 45) else (71, 149)))) else (if i.val < 221 then (if i.val < 219 then (if i.val < 218 then (6, 13) else (142, 173)) else (if i.val < 220 then (25, 204) else (43, 145))) else (if i.val < 223 then (if i.val < 222 then (70, 90) else (15, 69)) else (if i.val < 224 then (43, 239) else (15, 66))))) else (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (44, 178) else (if i.val < 227 then (32, 13) else (44, 249))) else (if i.val < 230 then (if i.val < 229 then (45, 138) else (45, 230)) else (if i.val < 231 then (102, 1) else (128, 84)))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then (74, 172) else (29, 143)) else (if i.val < 235 then (73, 52) else (136, 62))) else (if i.val < 238 then (if i.val < 237 then (129, 157) else (45, 23)) else (if i.val < 239 then (74, 92) else (129, 241))))))))) else (if i.val < 360 then (if i.val < 300 then (if i.val < 270 then (if i.val < 255 then (if i.val < 247 then (if i.val < 243 then (if i.val < 241 then (74, 48) else (if i.val < 242 then (103, 88) else (69, 108))) else (if i.val < 245 then (if i.val < 244 then (135, 206) else (23, 207)) else (if i.val < 246 then (86, 90) else (115, 226)))) else (if i.val < 251 then (if i.val < 249 then (if i.val < 248 then (131, 238) else (141, 223)) else (if i.val < 250 then (139, 222) else (143, 105))) else (if i.val < 253 then (if i.val < 252 then (144, 39) else (115, 112)) else (if i.val < 254 then (106, 157) else (133, 85))))) else (if i.val < 262 then (if i.val < 258 then (if i.val < 256 then (77, 5) else (if i.val < 257 then (63, 194) else (61, 138))) else (if i.val < 260 then (if i.val < 259 then (89, 50) else (140, 52)) else (if i.val < 261 then (133, 236) else (76, 176)))) else (if i.val < 266 then (if i.val < 264 then (if i.val < 263 then (116, 130) else (4, 131)) else (if i.val < 265 then (140, 91) else (11, 156))) else (if i.val < 268 then (if i.val < 267 then (144, 79) else (45, 161)) else (if i.val < 269 then (47, 125) else (142, 119)))))) else (if i.val < 285 then (if i.val < 277 then (if i.val < 273 then (if i.val < 271 then (85, 13) else (if i.val < 272 then (73, 252) else (90, 147))) else (if i.val < 275 then (if i.val < 274 then (130, 34) else (115, 135)) else (if i.val < 276 then (122, 121) else (114, 73)))) else (if i.val < 281 then (if i.val < 279 then (if i.val < 278 then (113, 211) else (140, 235)) else (if i.val < 280 then (100, 123) else (144, 146))) else (if i.val < 283 then (if i.val < 282 then (109, 212) else (85, 154)) else (if i.val < 284 then (86, 154) else (141, 75))))) else (if i.val < 292 then (if i.val < 288 then (if i.val < 286 then (108, 36) else (if i.val < 287 then (132, 66) else (95, 116))) else (if i.val < 290 then (if i.val < 289 then (140, 237) else (95, 7)) else (if i.val < 291 then (129, 119) else (117, 32)))) else (if i.val < 296 then (if i.val < 294 then (if i.val < 293 then (119, 37) else (140, 205)) else (if i.val < 295 then (117, 145) else (61, 107))) else (if i.val < 298 then (if i.val < 297 then (112, 142) else (134, 68)) else (if i.val < 299 then (82, 221) else (134, 15))))))) else (if i.val < 330 then (if i.val < 315 then (if i.val < 307 then (if i.val < 303 then (if i.val < 301 then (102, 189) else (if i.val < 302 then (112, 134) else (86, 54))) else (if i.val < 305 then (if i.val < 304 then (15, 80) else (118, 96)) else (if i.val < 306 then (0, 97) else (0, 99)))) else (if i.val < 311 then (if i.val < 309 then (if i.val < 308 then (139, 229) else (19, 241)) else (if i.val < 310 then (142, 127) else (111, 66))) else (if i.val < 313 then (if i.val < 312 then (133, 99) else (132, 171)) else (if i.val < 314 then (113, 199) else (142, 180))))) else (if i.val < 322 then (if i.val < 318 then (if i.val < 316 then (113, 170) else (if i.val < 317 then (143, 168) else (72, 111))) else (if i.val < 320 then (if i.val < 319 then (45, 83) else (98, 214)) else (if i.val < 321 then (121, 218) else (70, 229)))) else (if i.val < 326 then (if i.val < 324 then (if i.val < 323 then (143, 150) else (143, 232)) else (if i.val < 325 then (131, 7) else (97, 62))) else (if i.val < 328 then (if i.val < 327 then (138, 115) else (53, 191)) else (if i.val < 329 then (124, 119) else (140, 118)))))) else (if i.val < 345 then (if i.val < 337 then (if i.val < 333 then (if i.val < 331 then (47, 241) else (if i.val < 332 then (96, 217) else (135, 57))) else (if i.val < 335 then (if i.val < 334 then (46, 134) else (44, 129)) else (if i.val < 336 then (109, 121) else (121, 23)))) else (if i.val < 341 then (if i.val < 339 then (if i.val < 338 then (131, 221) else (130, 164)) else (if i.val < 340 then (52, 233) else (16, 25))) else (if i.val < 343 then (if i.val < 342 then (53, 123) else (76, 111)) else (if i.val < 344 then (29, 94) else (88, 242))))) else (if i.val < 352 then (if i.val < 348 then (if i.val < 346 then (80, 83) else (if i.val < 347 then (30, 104) else (144, 69))) else (if i.val < 350 then (if i.val < 349 then (50, 164) else (125, 39)) else (if i.val < 351 then (61, 133) else (139, 22)))) else (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then (112, 104) else (140, 30)) else (if i.val < 355 then (106, 214) else (106, 183))) else (if i.val < 358 then (if i.val < 357 then (138, 229) else (107, 11)) else (if i.val < 359 then (90, 172) else (136, 228)))))))) else (if i.val < 420 then (if i.val < 390 then (if i.val < 375 then (if i.val < 367 then (if i.val < 363 then (if i.val < 361 then (139, 242) else (if i.val < 362 then (143, 138) else (142, 141))) else (if i.val < 365 then (if i.val < 364 then (99, 6) else (111, 80)) else (if i.val < 366 then (116, 5) else (124, 236)))) else (if i.val < 371 then (if i.val < 369 then (if i.val < 368 then (45, 8) else (114, 217)) else (if i.val < 370 then (134, 211) else (63, 252))) else (if i.val < 373 then (if i.val < 372 then (101, 207) else (124, 46)) else (if i.val < 374 then (143, 121) else (53, 125))))) else (if i.val < 382 then (if i.val < 378 then (if i.val < 376 then (122, 99) else (if i.val < 377 then (41, 251) else (41, 219))) else (if i.val < 380 then (if i.val < 379 then (122, 67) else (53, 73)) else (if i.val < 381 then (39, 126) else (52, 235)))) else (if i.val < 386 then (if i.val < 384 then (if i.val < 383 then (40, 217) else (4, 94)) else (if i.val < 385 then (41, 229) else (43, 10))) else (if i.val < 388 then (if i.val < 387 then (4, 27) else (92, 166)) else (if i.val < 389 then (43, 37) else (52, 194)))))) else (if i.val < 405 then (if i.val < 397 then (if i.val < 393 then (if i.val < 391 then (53, 134) else (if i.val < 392 then (80, 137) else (53, 173))) else (if i.val < 395 then (if i.val < 394 then (128, 6) else (40, 190)) else (if i.val < 396 then (78, 95) else (105, 3)))) else (if i.val < 401 then (if i.val < 399 then (if i.val < 398 then (40, 35) else (5, 105)) else (if i.val < 400 then (133, 137) else (53, 175))) else (if i.val < 403 then (if i.val < 402 then (143, 239) else (107, 76)) else (if i.val < 404 then (139, 127) else (141, 225))))) else (if i.val < 412 then (if i.val < 408 then (if i.val < 406 then (103, 100) else (if i.val < 407 then (17, 207) else (112, 98))) else (if i.val < 410 then (if i.val < 409 then (97, 129) else (123, 19)) else (if i.val < 411 then (91, 3) else (131, 180)))) else (if i.val < 416 then (if i.val < 414 then (if i.val < 413 then (102, 81) else (121, 158)) else (if i.val < 415 then (142, 33) else (97, 14))) else (if i.val < 418 then (if i.val < 417 then (143, 224) else (72, 40)) else (if i.val < 419 then (101, 118) else (55, 222))))))) else (if i.val < 450 then (if i.val < 435 then (if i.val < 427 then (if i.val < 423 then (if i.val < 421 then (132, 158) else (if i.val < 422 then (132, 223) else (29, 121))) else (if i.val < 425 then (if i.val < 424 then (114, 117) else (33, 52)) else (if i.val < 426 then (123, 4) else (52, 165)))) else (if i.val < 431 then (if i.val < 429 then (if i.val < 428 then (0, 199) else (16, 236)) else (if i.val < 430 then (122, 114) else (114, 28))) else (if i.val < 433 then (if i.val < 432 then (127, 134) else (130, 146)) else (if i.val < 434 then (64, 244) else (141, 248))))) else (if i.val < 442 then (if i.val < 438 then (if i.val < 436 then (135, 34) else (if i.val < 437 then (126, 2) else (119, 230))) else (if i.val < 440 then (if i.val < 439 then (139, 109) else (127, 226)) else (if i.val < 441 then (132, 70) else (32, 122)))) else (if i.val < 446 then (if i.val < 444 then (if i.val < 443 then (111, 142) else (140, 47)) else (if i.val < 445 then (115, 68) else (139, 226))) else (if i.val < 448 then (if i.val < 447 then (139, 247) else (128, 60)) else (if i.val < 449 then (128, 31) else (141, 221)))))) else (if i.val < 465 then (if i.val < 457 then (if i.val < 453 then (if i.val < 451 then (138, 165) else (if i.val < 452 then (51, 100) else (100, 15))) else (if i.val < 455 then (if i.val < 454 then (130, 115) else (124, 209)) else (if i.val < 456 then (142, 102) else (134, 103)))) else (if i.val < 461 then (if i.val < 459 then (if i.val < 458 then (0, 101) else (124, 43)) else (if i.val < 460 then (121, 69) else (134, 214))) else (if i.val < 463 then (if i.val < 462 then (112, 220) else (134, 203)) else (if i.val < 464 then (100, 244) else (136, 111))))) else (if i.val < 472 then (if i.val < 468 then (if i.val < 466 then (131, 163) else (if i.val < 467 then (94, 141) else (129, 20))) else (if i.val < 470 then (if i.val < 469 then (135, 30) else (86, 118)) else (if i.val < 471 then (128, 1) else (138, 233)))) else (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then (95, 198) else (51, 200)) else (if i.val < 475 then (113, 66) else (143, 230))) else (if i.val < 478 then (if i.val < 477 then (98, 229) else (132, 136)) else (if i.val < 479 then (79, 255) else (79, 208))))))))))

def g32p_supplierGroup25_classify : Fin 480 → Fin 102 :=
  fun i => (if i.val < 240 then (if i.val < 120 then (if i.val < 60 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 47 else 18)) else (if i.val < 5 then (if i.val < 4 then 16 else 47) else (if i.val < 6 then 47 else 22))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then 60 else 60) else (if i.val < 10 then 60 else 47)) else (if i.val < 13 then (if i.val < 12 then 26 else 73) else (if i.val < 14 then 73 else 73)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then 16 else (if i.val < 17 then 73 else 16)) else (if i.val < 20 then (if i.val < 19 then 16 else 37) else (if i.val < 21 then 26 else 26))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then 26 else 73) else (if i.val < 25 then 26 else 73)) else (if i.val < 28 then (if i.val < 27 then 73 else 26) else (if i.val < 29 then 22 else 73))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then 73 else (if i.val < 32 then 60 else 73)) else (if i.val < 35 then (if i.val < 34 then 65 else 65) else (if i.val < 36 then 65 else 47))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then 65 else 26) else (if i.val < 40 then 47 else 65)) else (if i.val < 43 then (if i.val < 42 then 47 else 26) else (if i.val < 44 then 47 else 22)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then 26 else (if i.val < 47 then 47 else 26)) else (if i.val < 50 then (if i.val < 49 then 73 else 47) else (if i.val < 51 then 73 else 22))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then 47 else 73) else (if i.val < 55 then 73 else 73)) else (if i.val < 58 then (if i.val < 57 then 34 else 73) else (if i.val < 59 then 34 else 34)))))) else (if i.val < 90 then (if i.val < 75 then (if i.val < 67 then (if i.val < 63 then (if i.val < 61 then 73 else (if i.val < 62 then 34 else 34)) else (if i.val < 65 then (if i.val < 64 then 34 else 26) else (if i.val < 66 then 34 else 34))) else (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then 34 else 34) else (if i.val < 70 then 26 else 34)) else (if i.val < 73 then (if i.val < 72 then 34 else 26) else (if i.val < 74 then 34 else 26)))) else (if i.val < 82 then (if i.val < 78 then (if i.val < 76 then 34 else (if i.val < 77 then 26 else 26)) else (if i.val < 80 then (if i.val < 79 then 73 else 16) else (if i.val < 81 then 26 else 26))) else (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then 26 else 73) else (if i.val < 85 then 26 else 22)) else (if i.val < 88 then (if i.val < 87 then 73 else 26) else (if i.val < 89 then 73 else 22))))) else (if i.val < 105 then (if i.val < 97 then (if i.val < 93 then (if i.val < 91 then 73 else (if i.val < 92 then 34 else 22)) else (if i.val < 95 then (if i.val < 94 then 73 else 22) else (if i.val < 96 then 73 else 34))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then 22 else 73) else (if i.val < 100 then 34 else 22)) else (if i.val < 103 then (if i.val < 102 then 73 else 34) else (if i.val < 104 then 22 else 65)))) else (if i.val < 112 then (if i.val < 108 then (if i.val < 106 then 73 else (if i.val < 107 then 65 else 22)) else (if i.val < 110 then (if i.val < 109 then 65 else 47) else (if i.val < 111 then 65 else 47))) else (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 22 else 60) else (if i.val < 115 then 60 else 60)) else (if i.val < 118 then (if i.val < 117 then 47 else 60) else (if i.val < 119 then 47 else 47))))))) else (if i.val < 180 then (if i.val < 150 then (if i.val < 135 then (if i.val < 127 then (if i.val < 123 then (if i.val < 121 then 60 else (if i.val < 122 then 26 else 47)) else (if i.val < 125 then (if i.val < 124 then 47 else 22) else (if i.val < 126 then 26 else 26))) else (if i.val < 131 then (if i.val < 129 then (if i.val < 128 then 47 else 47) else (if i.val < 130 then 26 else 26)) else (if i.val < 133 then (if i.val < 132 then 22 else 47) else (if i.val < 134 then 47 else 26)))) else (if i.val < 142 then (if i.val < 138 then (if i.val < 136 then 22 else (if i.val < 137 then 26 else 22)) else (if i.val < 140 then (if i.val < 139 then 47 else 22) else (if i.val < 141 then 22 else 26))) else (if i.val < 146 then (if i.val < 144 then (if i.val < 143 then 26 else 73) else (if i.val < 145 then 22 else 96)) else (if i.val < 148 then (if i.val < 147 then 22 else 22) else (if i.val < 149 then 22 else 60))))) else (if i.val < 165 then (if i.val < 157 then (if i.val < 153 then (if i.val < 151 then 22 else (if i.val < 152 then 60 else 60)) else (if i.val < 155 then (if i.val < 154 then 22 else 16) else (if i.val < 156 then 60 else 60))) else (if i.val < 161 then (if i.val < 159 then (if i.val < 158 then 26 else 16) else (if i.val < 160 then 16 else 60)) else (if i.val < 163 then (if i.val < 162 then 60 else 16) else (if i.val < 164 then 16 else 60)))) else (if i.val < 172 then (if i.val < 168 then (if i.val < 166 then 60 else (if i.val < 167 then 16 else 47)) else (if i.val < 170 then (if i.val < 169 then 16 else 47) else (if i.val < 171 then 60 else 47))) else (if i.val < 176 then (if i.val < 174 then (if i.val < 173 then 47 else 16) else (if i.val < 175 then 16 else 47)) else (if i.val < 178 then (if i.val < 177 then 16 else 22) else (if i.val < 179 then 60 else 82)))))) else (if i.val < 210 then (if i.val < 195 then (if i.val < 187 then (if i.val < 183 then (if i.val < 181 then 82 else (if i.val < 182 then 82 else 73)) else (if i.val < 185 then (if i.val < 184 then 82 else 22) else (if i.val < 186 then 73 else 82))) else (if i.val < 191 then (if i.val < 189 then (if i.val < 188 then 73 else 22) else (if i.val < 190 then 73 else 22)) else (if i.val < 193 then (if i.val < 192 then 73 else 22) else (if i.val < 194 then 73 else 22)))) else (if i.val < 202 then (if i.val < 198 then (if i.val < 196 then 73 else (if i.val < 197 then 22 else 73)) else (if i.val < 200 then (if i.val < 199 then 22 else 16) else (if i.val < 201 then 73 else 16))) else (if i.val < 206 then (if i.val < 204 then (if i.val < 203 then 22 else 16) else (if i.val < 205 then 16 else 22)) else (if i.val < 208 then (if i.val < 207 then 73 else 16) else (if i.val < 209 then 22 else 26))))) else (if i.val < 225 then (if i.val < 217 then (if i.val < 213 then (if i.val < 211 then 73 else (if i.val < 212 then 60 else 60)) else (if i.val < 215 then (if i.val < 214 then 60 else 13) else (if i.val < 216 then 60 else 13))) else (if i.val < 221 then (if i.val < 219 then (if i.val < 218 then 13 else 60) else (if i.val < 220 then 13 else 13)) else (if i.val < 223 then (if i.val < 222 then 13 else 13) else (if i.val < 224 then 13 else 13)))) else (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then 13 else (if i.val < 227 then 13 else 13)) else (if i.val < 230 then (if i.val < 229 then 13 else 13) else (if i.val < 231 then 13 else 73))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 13 else 73) else (if i.val < 235 then 13 else 73)) else (if i.val < 238 then (if i.val < 237 then 73 else 13) else (if i.val < 239 then 13 else 73)))))))) else (if i.val < 360 then (if i.val < 300 then (if i.val < 270 then (if i.val < 255 then (if i.val < 247 then (if i.val < 243 then (if i.val < 241 then 13 else (if i.val < 242 then 60 else 47)) else (if i.val < 245 then (if i.val < 244 then 22 else 22) else (if i.val < 246 then 22 else 60))) else (if i.val < 251 then (if i.val < 249 then (if i.val < 248 then 22 else 16) else (if i.val < 250 then 60 else 22)) else (if i.val < 253 then (if i.val < 252 then 60 else 16) else (if i.val < 254 then 60 else 16)))) else (if i.val < 262 then (if i.val < 258 then (if i.val < 256 then 60 else (if i.val < 257 then 16 else 60)) else (if i.val < 260 then (if i.val < 259 then 16 else 60) else (if i.val < 261 then 16 else 60))) else (if i.val < 266 then (if i.val < 264 then (if i.val < 263 then 16 else 82) else (if i.val < 265 then 60 else 82)) else (if i.val < 268 then (if i.val < 267 then 16 else 82) else (if i.val < 269 then 82 else 16))))) else (if i.val < 285 then (if i.val < 277 then (if i.val < 273 then (if i.val < 271 then 60 else (if i.val < 272 then 82 else 16)) else (if i.val < 275 then (if i.val < 274 then 73 else 16) else (if i.val < 276 then 26 else 26))) else (if i.val < 281 then (if i.val < 279 then (if i.val < 278 then 26 else 73) else (if i.val < 280 then 26 else 73)) else (if i.val < 283 then (if i.val < 282 then 73 else 26) else (if i.val < 284 then 22 else 73)))) else (if i.val < 292 then (if i.val < 288 then (if i.val < 286 then 73 else (if i.val < 287 then 22 else 22)) else (if i.val < 290 then (if i.val < 289 then 73 else 73) else (if i.val < 291 then 22 else 22))) else (if i.val < 296 then (if i.val < 294 then (if i.val < 293 then 73 else 73) else (if i.val < 295 then 22 else 16)) else (if i.val < 298 then (if i.val < 297 then 22 else 16) else (if i.val < 299 then 73 else 16)))))) else (if i.val < 330 then (if i.val < 315 then (if i.val < 307 then (if i.val < 303 then (if i.val < 301 then 16 else (if i.val < 302 then 22 else 22)) else (if i.val < 305 then (if i.val < 304 then 16 else 22) else (if i.val < 306 then 97 else 99))) else (if i.val < 311 then (if i.val < 309 then (if i.val < 308 then 16 else 16) else (if i.val < 310 then 16 else 26)) else (if i.val < 313 then (if i.val < 312 then 16 else 26) else (if i.val < 314 then 26 else 16)))) else (if i.val < 322 then (if i.val < 318 then (if i.val < 316 then 47 else (if i.val < 317 then 26 else 26)) else (if i.val < 320 then (if i.val < 319 then 47 else 47) else (if i.val < 321 then 26 else 26))) else (if i.val < 326 then (if i.val < 324 then (if i.val < 323 then 47 else 47) else (if i.val < 325 then 26 else 26)) else (if i.val < 328 then (if i.val < 327 then 47 else 73) else (if i.val < 329 then 47 else 73))))) else (if i.val < 345 then (if i.val < 337 then (if i.val < 333 then (if i.val < 331 then 26 else (if i.val < 332 then 73 else 73)) else (if i.val < 335 then (if i.val < 334 then 47 else 47) else (if i.val < 336 then 73 else 47))) else (if i.val < 341 then (if i.val < 339 then (if i.val < 338 then 16 else 26) else (if i.val < 340 then 18 else 18)) else (if i.val < 343 then (if i.val < 342 then 18 else 60) else (if i.val < 344 then 18 else 16)))) else (if i.val < 352 then (if i.val < 348 then (if i.val < 346 then 60 else (if i.val < 347 then 18 else 60)) else (if i.val < 350 then (if i.val < 349 then 16 else 60) else (if i.val < 351 then 16 else 60))) else (if i.val < 356 then (if i.val < 354 then (if i.val < 353 then 16 else 60) else (if i.val < 355 then 16 else 60)) else (if i.val < 358 then (if i.val < 357 then 16 else 60) else (if i.val < 359 then 16 else 47))))))) else (if i.val < 420 then (if i.val < 390 then (if i.val < 375 then (if i.val < 367 then (if i.val < 363 then (if i.val < 361 then 60 else (if i.val < 362 then 47 else 16)) else (if i.val < 365 then (if i.val < 364 then 47 else 47) else (if i.val < 366 then 16 else 60))) else (if i.val < 371 then (if i.val < 369 then (if i.val < 368 then 47 else 16) else (if i.val < 370 then 22 else 60)) else (if i.val < 373 then (if i.val < 372 then 26 else 26) else (if i.val < 374 then 26 else 69)))) else (if i.val < 382 then (if i.val < 378 then (if i.val < 376 then 26 else (if i.val < 377 then 69 else 69)) else (if i.val < 380 then (if i.val < 379 then 26 else 69) else (if i.val < 381 then 69 else 69))) else (if i.val < 386 then (if i.val < 384 then (if i.val < 383 then 69 else 69) else (if i.val < 385 then 69 else 69)) else (if i.val < 388 then (if i.val < 387 then 69 else 69) else (if i.val < 389 then 69 else 69))))) else (if i.val < 405 then (if i.val < 397 then (if i.val < 393 then (if i.val < 391 then 69 else (if i.val < 392 then 60 else 69)) else (if i.val < 395 then (if i.val < 394 then 60 else 69) else (if i.val < 396 then 60 else 60))) else (if i.val < 401 then (if i.val < 399 then (if i.val < 398 then 69 else 69) else (if i.val < 400 then 60 else 69)) else (if i.val < 403 then (if i.val < 402 then 26 else 73) else (if i.val < 404 then 16 else 16)))) else (if i.val < 412 then (if i.val < 408 then (if i.val < 406 then 16 else (if i.val < 407 then 26 else 16)) else (if i.val < 410 then (if i.val < 409 then 47 else 26) else (if i.val < 411 then 16 else 26))) else (if i.val < 416 then (if i.val < 414 then (if i.val < 413 then 47 else 26) else (if i.val < 415 then 47 else 26)) else (if i.val < 418 then (if i.val < 417 then 47 else 26) else (if i.val < 419 then 26 else 47)))))) else (if i.val < 450 then (if i.val < 435 then (if i.val < 427 then (if i.val < 423 then (if i.val < 421 then 26 else (if i.val < 422 then 47 else 18)) else (if i.val < 425 then (if i.val < 424 then 26 else 18) else (if i.val < 426 then 47 else 18))) else (if i.val < 431 then (if i.val < 429 then (if i.val < 428 then 18 else 47) else (if i.val < 430 then 26 else 47)) else (if i.val < 433 then (if i.val < 432 then 60 else 47) else (if i.val < 434 then 22 else 22)))) else (if i.val < 442 then (if i.val < 438 then (if i.val < 436 then 22 else (if i.val < 437 then 60 else 22)) else (if i.val < 440 then (if i.val < 439 then 60 else 60) else (if i.val < 441 then 22 else 16))) else (if i.val < 446 then (if i.val < 444 then (if i.val < 443 then 60 else 60) else (if i.val < 445 then 16 else 16)) else (if i.val < 448 then (if i.val < 447 then 60 else 60) else (if i.val < 449 then 60 else 16))))) else (if i.val < 465 then (if i.val < 457 then (if i.val < 453 then (if i.val < 451 then 47 else (if i.val < 452 then 60 else 47)) else (if i.val < 455 then (if i.val < 454 then 47 else 16) else (if i.val < 456 then 16 else 16))) else (if i.val < 461 then (if i.val < 459 then (if i.val < 458 then 101 else 47) else (if i.val < 460 then 47 else 22)) else (if i.val < 463 then (if i.val < 462 then 22 else 22) else (if i.val < 464 then 47 else 73)))) else (if i.val < 472 then (if i.val < 468 then (if i.val < 466 then 22 else (if i.val < 467 then 22 else 73)) else (if i.val < 470 then (if i.val < 469 then 22 else 22) else (if i.val < 471 then 60 else 60))) else (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then 73 else 65) else (if i.val < 475 then 47 else 47)) else (if i.val < 478 then (if i.val < 477 then 47 else 47) else (if i.val < 479 then 34 else 34)))))))))

def g32p_supplierGroup25_support : Finset (Fin 102) :=
  {0, 13, 16, 18, 22, 26, 34, 37, 47, 60, 65, 69, 73, 82, 96, 97, 99, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup25_matrix_000 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 0 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 0 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 0 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 0 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 0 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_001 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 1 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 1 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 1 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 1 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 1 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_002 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 2 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 2 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 2 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 2 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 2 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_003 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 3 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 3 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 3 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 3 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 3 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_004 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 4 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 4 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 4 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 4 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 4 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_005 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 5 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 5 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 5 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 5 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 5 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_006 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 6 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 6 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 6 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 6 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 6 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_007 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 7 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 7 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 7 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 7 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 7 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_008 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 8 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 8 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 8 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 8 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 8 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_009 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 9 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 9 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 9 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 9 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 9 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_010 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 10 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 10 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 10 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 10 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 10 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_011 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 11 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 11 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 11 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 11 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 11 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_012 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 12 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 12 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 12 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 12 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 12 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_013 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 13 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 13 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 13 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 13 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 13 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_014 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 14 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 14 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 14 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 14 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 14 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_015 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 15 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 15 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 15 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 15 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 15 r) ∈ g32p_supplierGroup25_support := by
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

theorem g32p_supplierGroup25_matrix_016 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 16 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 16 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 16 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 16 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 16 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_017 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 17 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 17 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 17 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 17 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 17 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_018 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 18 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 18 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 18 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 18 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 18 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_019 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 19 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 19 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 19 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 19 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 19 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_020 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 20 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 20 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 20 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 20 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 20 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_021 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 21 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 21 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 21 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 21 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 21 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_022 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 22 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 22 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 22 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 22 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 22 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_023 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 23 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 23 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 23 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 23 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 23 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_024 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 24 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 24 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 24 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_024 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 24 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 24 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 24 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_024 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 24 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_025 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 25 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 25 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 25 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_025 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 25 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 25 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 25 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_025 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 25 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_026 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 26 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 26 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 26 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_026 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 26 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 26 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 26 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_026 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 26 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_027 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 27 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 27 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 27 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_027 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 27 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 27 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 27 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_027 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 27 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_028 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 28 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 28 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 28 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_028 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 28 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 28 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 28 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_028 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 28 r) ∈ g32p_supplierGroup25_support := by
  decide +kernel

theorem g32p_supplierGroup25_matrix_029 : ∀ r : Fin 16,
    g32p_row34_groupNodes (g32p_finBlockIndex 480 29 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 29 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 29 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup25_class_029 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup25_source (g32p_finBlockIndex 480 29 r)).1 (g32p_supplierGroup25_source (g32p_finBlockIndex 480 29 r)).2 =
      g32p_supplierGroup25_classify (g32p_finBlockIndex 480 29 r) := by
  decide +kernel

theorem g32p_supplierGroup25_support_029 : ∀ r : Fin 16,
    g32p_supplierGroup25_classify (g32p_finBlockIndex 480 29 r) ∈ g32p_supplierGroup25_support := by
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

theorem g32p_supplierGroup25_matrix (i : Fin 480) :
    g32p_row34_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source i).1 (g32p_supplierGroup25_source i).2 := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row34_groupNodes i =
      g32p_supplierForest_nodes (g32p_supplierGroup25_source i).1 (g32p_supplierGroup25_source i).2) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup25_matrix_000 r
  · exact g32p_supplierGroup25_matrix_001 r
  · exact g32p_supplierGroup25_matrix_002 r
  · exact g32p_supplierGroup25_matrix_003 r
  · exact g32p_supplierGroup25_matrix_004 r
  · exact g32p_supplierGroup25_matrix_005 r
  · exact g32p_supplierGroup25_matrix_006 r
  · exact g32p_supplierGroup25_matrix_007 r
  · exact g32p_supplierGroup25_matrix_008 r
  · exact g32p_supplierGroup25_matrix_009 r
  · exact g32p_supplierGroup25_matrix_010 r
  · exact g32p_supplierGroup25_matrix_011 r
  · exact g32p_supplierGroup25_matrix_012 r
  · exact g32p_supplierGroup25_matrix_013 r
  · exact g32p_supplierGroup25_matrix_014 r
  · exact g32p_supplierGroup25_matrix_015 r
  · exact g32p_supplierGroup25_matrix_016 r
  · exact g32p_supplierGroup25_matrix_017 r
  · exact g32p_supplierGroup25_matrix_018 r
  · exact g32p_supplierGroup25_matrix_019 r
  · exact g32p_supplierGroup25_matrix_020 r
  · exact g32p_supplierGroup25_matrix_021 r
  · exact g32p_supplierGroup25_matrix_022 r
  · exact g32p_supplierGroup25_matrix_023 r
  · exact g32p_supplierGroup25_matrix_024 r
  · exact g32p_supplierGroup25_matrix_025 r
  · exact g32p_supplierGroup25_matrix_026 r
  · exact g32p_supplierGroup25_matrix_027 r
  · exact g32p_supplierGroup25_matrix_028 r
  · exact g32p_supplierGroup25_matrix_029 r

theorem g32p_supplierGroup25_class (i : Fin 480) :
    g32p_supplierForest_classes (g32p_supplierGroup25_source i).1 (g32p_supplierGroup25_source i).2 =
      g32p_supplierGroup25_classify i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierForest_classes (g32p_supplierGroup25_source i).1 (g32p_supplierGroup25_source i).2 =
      g32p_supplierGroup25_classify i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup25_class_000 r
  · exact g32p_supplierGroup25_class_001 r
  · exact g32p_supplierGroup25_class_002 r
  · exact g32p_supplierGroup25_class_003 r
  · exact g32p_supplierGroup25_class_004 r
  · exact g32p_supplierGroup25_class_005 r
  · exact g32p_supplierGroup25_class_006 r
  · exact g32p_supplierGroup25_class_007 r
  · exact g32p_supplierGroup25_class_008 r
  · exact g32p_supplierGroup25_class_009 r
  · exact g32p_supplierGroup25_class_010 r
  · exact g32p_supplierGroup25_class_011 r
  · exact g32p_supplierGroup25_class_012 r
  · exact g32p_supplierGroup25_class_013 r
  · exact g32p_supplierGroup25_class_014 r
  · exact g32p_supplierGroup25_class_015 r
  · exact g32p_supplierGroup25_class_016 r
  · exact g32p_supplierGroup25_class_017 r
  · exact g32p_supplierGroup25_class_018 r
  · exact g32p_supplierGroup25_class_019 r
  · exact g32p_supplierGroup25_class_020 r
  · exact g32p_supplierGroup25_class_021 r
  · exact g32p_supplierGroup25_class_022 r
  · exact g32p_supplierGroup25_class_023 r
  · exact g32p_supplierGroup25_class_024 r
  · exact g32p_supplierGroup25_class_025 r
  · exact g32p_supplierGroup25_class_026 r
  · exact g32p_supplierGroup25_class_027 r
  · exact g32p_supplierGroup25_class_028 r
  · exact g32p_supplierGroup25_class_029 r

theorem g32p_supplierGroup25_support_mem (i : Fin 480) :
    g32p_supplierGroup25_classify i ∈ g32p_supplierGroup25_support := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_supplierGroup25_classify i ∈ g32p_supplierGroup25_support) ?_ i
  intro q r
  fin_cases q
  · exact g32p_supplierGroup25_support_000 r
  · exact g32p_supplierGroup25_support_001 r
  · exact g32p_supplierGroup25_support_002 r
  · exact g32p_supplierGroup25_support_003 r
  · exact g32p_supplierGroup25_support_004 r
  · exact g32p_supplierGroup25_support_005 r
  · exact g32p_supplierGroup25_support_006 r
  · exact g32p_supplierGroup25_support_007 r
  · exact g32p_supplierGroup25_support_008 r
  · exact g32p_supplierGroup25_support_009 r
  · exact g32p_supplierGroup25_support_010 r
  · exact g32p_supplierGroup25_support_011 r
  · exact g32p_supplierGroup25_support_012 r
  · exact g32p_supplierGroup25_support_013 r
  · exact g32p_supplierGroup25_support_014 r
  · exact g32p_supplierGroup25_support_015 r
  · exact g32p_supplierGroup25_support_016 r
  · exact g32p_supplierGroup25_support_017 r
  · exact g32p_supplierGroup25_support_018 r
  · exact g32p_supplierGroup25_support_019 r
  · exact g32p_supplierGroup25_support_020 r
  · exact g32p_supplierGroup25_support_021 r
  · exact g32p_supplierGroup25_support_022 r
  · exact g32p_supplierGroup25_support_023 r
  · exact g32p_supplierGroup25_support_024 r
  · exact g32p_supplierGroup25_support_025 r
  · exact g32p_supplierGroup25_support_026 r
  · exact g32p_supplierGroup25_support_027 r
  · exact g32p_supplierGroup25_support_028 r
  · exact g32p_supplierGroup25_support_029 r

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row34_supplierClassifier : Fin 480 → Fin 102 := g32p_supplierGroup25_classify

theorem g32p_row34_groupEquiv_isConj (i : Fin 480) :
    IsConj (g32p_row34_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row34_supplierClassifier i)) := by
  have h := g32p_supplierForest_actual (g32p_supplierGroup25_source i).1 (g32p_supplierGroup25_source i).2
  rw [g32p_supplierGroup25_class] at h
  apply g32p_supplier_class_of_matrix _ _ _ ?_ h
  rw [g32p_row34_groupEquiv_map]
  exact congrArg (fun m : HurwitzPrymRex_Mat =>
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega m)) (g32p_supplierGroup25_matrix i)

def g32p_row34_supplierClass (h : (g32p_recordedSuppliers 33).H) : Fin 102 :=
  g32p_row34_supplierClassifier (g32p_row34_groupEquiv.symm h)

theorem g32p_row34_supplierClass_isConj (h : (g32p_recordedSuppliers 33).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row34_supplierClass h)) := by
  have he : (g32p_row34_groupEquiv (g32p_row34_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : (g32p_recordedSuppliers 33).H => (a : g32p_G))
      (g32p_row34_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row34_supplierClassifier (g32p_row34_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row34_groupEquiv_isConj (g32p_row34_groupEquiv.symm h)

theorem g32p_row34_supplierClass_iff (h : (g32p_recordedSuppliers 33).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row34_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row34_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row34_supplierClass_isConj h).symm

theorem g32p_row34_supplierClass_mem_support (h : (g32p_recordedSuppliers 33).H) :
    g32p_row34_supplierClass h ∈ g32p_supplierGroup25_support :=
  g32p_supplierGroup25_support_mem (g32p_row34_groupEquiv.symm h)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row34_traceCoefficients_000 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 0 = [1] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 0) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 0) (g32p_literalTraceValue 33 0)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  rw [g32p_row34_traceCoefficients_000]
  decide +kernel

theorem g32p_row34_traceCoefficients_013 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 13 = [0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_013 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 13) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 13) (g32p_literalTraceValue 33 13)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  rw [g32p_row34_traceCoefficients_013]
  decide +kernel

theorem g32p_row34_traceCoefficients_016 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 16 = [0, 16, 0, 0, 16, 0, 0, 16, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_016 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 16) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 16) (g32p_literalTraceValue 33 16)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-480, 0, 0, 480, 480, 480] = true := by
  rw [g32p_row34_traceCoefficients_016]
  decide +kernel

theorem g32p_row34_traceCoefficients_018 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 18 = [10] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_018 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 18) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 18) (g32p_literalTraceValue 33 18)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  rw [g32p_row34_traceCoefficients_018]
  decide +kernel

theorem g32p_row34_traceCoefficients_022 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 22 = [0, 0, 0, 16, 0, 0, 16, 0, 0, 16, 0, 0, 16] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_022 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 22) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 22) (g32p_literalTraceValue 33 22)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [480, 480, 480, 480, 480] = true := by
  rw [g32p_row34_traceCoefficients_022]
  decide +kernel

theorem g32p_row34_traceCoefficients_026 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 26 = [0, 0, 16, 0, 0, 0, 0, 0, 16, 0, 0, 16, 0, 0, 16] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_026 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 26) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 26) (g32p_literalTraceValue 33 26)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [0, 0, 480, 480, 480, 480, 480] = true := by
  rw [g32p_row34_traceCoefficients_026]
  decide +kernel

theorem g32p_row34_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 34 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 34) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 34) (g32p_literalTraceValue 33 34)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [5760, 5760, 5760] = true := by
  rw [g32p_row34_traceCoefficients_034]
  decide +kernel

theorem g32p_row34_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 37 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 37) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 37) (g32p_literalTraceValue 33 37)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row34_traceCoefficients_037]
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

theorem g32p_row34_traceCoefficients_047 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 47 = [0, 0, 16, 0, 0, 0, 0, 0, 16, 0, 0, 16, 0, 0, 16] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_047 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 47) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 47) (g32p_literalTraceValue 33 47)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [0, 0, 480, 480, 480, 480, 480] = true := by
  rw [g32p_row34_traceCoefficients_047]
  decide +kernel

theorem g32p_row34_traceCoefficients_060 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 60 = [0, 16, 0, 0, 16, 0, 0, 16, 0, 0, 0, 0, 0, 16] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_060 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 60) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 60) (g32p_literalTraceValue 33 60)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [-480, 0, 0, 480, 480, 480] = true := by
  rw [g32p_row34_traceCoefficients_060]
  decide +kernel

theorem g32p_row34_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 65 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 65) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 65) (g32p_literalTraceValue 33 65)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [17280, 17280, 17280] = true := by
  rw [g32p_row34_traceCoefficients_065]
  decide +kernel

theorem g32p_row34_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 69 = [20] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 69) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 69) (g32p_literalTraceValue 33 69)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  rw [g32p_row34_traceCoefficients_069]
  decide +kernel

theorem g32p_row34_traceCoefficients_073 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 73 = [0, 0, 0, 16, 0, 0, 16, 0, 0, 16, 0, 0, 16] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_073 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 73) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 73) (g32p_literalTraceValue 33 73)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [480, 480, 480, 480, 480] = true := by
  rw [g32p_row34_traceCoefficients_073]
  decide +kernel

theorem g32p_row34_traceCoefficients_082 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 82 = [0, 0, 0, 0, 0, 10] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 82) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 82) (g32p_literalTraceValue 33 82)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  rw [g32p_row34_traceCoefficients_082]
  decide +kernel

theorem g32p_row34_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 96 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 96) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 96) (g32p_literalTraceValue 33 96)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  rw [g32p_row34_traceCoefficients_096]
  decide +kernel

theorem g32p_row34_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 97 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 97) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 97) (g32p_literalTraceValue 33 97)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  rw [g32p_row34_traceCoefficients_097]
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

theorem g32p_row34_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 99 = [1] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_099 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 99) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 99) (g32p_literalTraceValue 33 99)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [] = true := by
  rw [g32p_row34_traceCoefficients_099]
  decide +kernel

theorem g32p_row34_traceCoefficients_101 :
    g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 101 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem g32p_row34_tracePolynomial_101 :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer 101) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) 101) (g32p_literalTraceValue 33 101)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row34_traceCoefficients_101]
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

def g32p_row34_generatorIndex : Fin 8 → Fin 408 :=
  ![33, 84, 135, 186, 270, 271, 372, 373]

theorem g32p_row34_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_supplierGroup25_support)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 33 conjugate).character (g32p_literalRepresentative c) = 0 :=
  g32p_supplier_coinduced_zero 33 g32p_row34_supplierClass
    g32p_row34_supplierClass_isConj g32p_supplierGroup25_support g32p_row34_supplierClass_mem_support
    g32p_literalRepresentative_classes_injective c hc conjugate

theorem g32p_row34_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_supplierGroup25_support) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row34_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_supplier_induction_zero 33 c false (g32p_row34_coinduced_zero c hc false) 0
  · exact g32p_supplier_induction_zero 33 c true (g32p_row34_coinduced_zero c hc true) 0
  · exact g32p_supplier_induction_zero 33 c false (g32p_row34_coinduced_zero c hc false) 1
  · exact g32p_supplier_induction_zero 33 c true (g32p_row34_coinduced_zero c hc true) 1
  · exact g32p_supplier_induction_zero 33 c false (g32p_row34_coinduced_zero c hc false) 2
  · exact g32p_supplier_induction_zero 33 c false (g32p_row34_coinduced_zero c hc false) 3
  · exact g32p_supplier_induction_zero 33 c true (g32p_row34_coinduced_zero c hc true) 2
  · exact g32p_supplier_induction_zero 33 c true (g32p_row34_coinduced_zero c hc true) 3

theorem g32p_row34_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_supplierGroup25_support →
      g32p_literalTraceValue (g32p_row34_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row34_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_supplierGroup25_support →
      g32p_literalTraceValue (g32p_row34_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row34_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_supplierGroup25_support →
      g32p_literalTraceValue (g32p_row34_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row34_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_supplierGroup25_support →
      g32p_literalTraceValue (g32p_row34_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row34_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_supplierGroup25_support →
      g32p_literalTraceValue (g32p_row34_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row34_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_supplierGroup25_support →
      g32p_literalTraceValue (g32p_row34_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row34_zeroTrace_block_06 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 6 r ∉ g32p_supplierGroup25_support →
      g32p_literalTraceValue (g32p_row34_generatorIndex k) (g32p_finBlockIndex 102 6 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

theorem g32p_row34_zeroTrace_arithmetic (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup25_support) :
    g32p_literalTraceValue (g32p_row34_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  apply g32p_forall_fin_blocks (fun c => c ∉ g32p_supplierGroup25_support →
    g32p_literalTraceValue (g32p_row34_generatorIndex k) c = (⟨0, 0⟩ : HurwitzPrymRex_Zw)) ?_ c hc
  intro q r
  fin_cases q
  · exact g32p_row34_zeroTrace_block_00 r k
  · exact g32p_row34_zeroTrace_block_01 r k
  · exact g32p_row34_zeroTrace_block_02 r k
  · exact g32p_row34_zeroTrace_block_03 r k
  · exact g32p_row34_zeroTrace_block_04 r k
  · exact g32p_row34_zeroTrace_block_05 r k
  · exact g32p_row34_zeroTrace_block_06 r k

theorem g32p_row34_literalTrace_actual (c : Fin 102) (k : Fin 8)
    (hc : c ∉ g32p_supplierGroup25_support) :
    (g32p_recordedInductionGenerators (g32p_row34_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row34_generatorIndex k) c) := by
  rw [g32p_row34_recordedGenerator_zero c hc k, g32p_row34_zeroTrace_arithmetic c k hc]
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

def g32p_row34_traceQuotient : Fin 102 → List ℤ :=
  fun i => (if i.val < 51 then (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then [] else (if i.val < 2 then [] else [])) else (if i.val < 4 then [] else (if i.val < 5 then [] else []))) else (if i.val < 9 then (if i.val < 7 then [] else (if i.val < 8 then [] else [])) else (if i.val < 10 then [] else (if i.val < 11 then [] else [])))) else (if i.val < 18 then (if i.val < 15 then (if i.val < 13 then [] else (if i.val < 14 then [] else [])) else (if i.val < 16 then [] else (if i.val < 17 then [-480, 0, 0, 480, 480, 480] else []))) else (if i.val < 21 then (if i.val < 19 then [] else (if i.val < 20 then [] else [])) else (if i.val < 23 then (if i.val < 22 then [] else [480, 480, 480, 480, 480]) else (if i.val < 24 then [] else []))))) else (if i.val < 38 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then [] else (if i.val < 27 then [0, 0, 480, 480, 480, 480, 480] else [])) else (if i.val < 29 then [] else (if i.val < 30 then [] else []))) else (if i.val < 34 then (if i.val < 32 then [] else (if i.val < 33 then [] else [])) else (if i.val < 36 then (if i.val < 35 then [5760, 5760, 5760] else []) else (if i.val < 37 then [] else [155520, 155520, 155520])))) else (if i.val < 44 then (if i.val < 41 then (if i.val < 39 then [] else (if i.val < 40 then [] else [])) else (if i.val < 42 then [] else (if i.val < 43 then [] else []))) else (if i.val < 47 then (if i.val < 45 then [] else (if i.val < 46 then [] else [])) else (if i.val < 49 then (if i.val < 48 then [0, 0, 480, 480, 480, 480, 480] else []) else (if i.val < 50 then [] else [])))))) else (if i.val < 76 then (if i.val < 63 then (if i.val < 57 then (if i.val < 54 then (if i.val < 52 then [] else (if i.val < 53 then [] else [])) else (if i.val < 55 then [] else (if i.val < 56 then [] else []))) else (if i.val < 60 then (if i.val < 58 then [] else (if i.val < 59 then [] else [])) else (if i.val < 61 then [-480, 0, 0, 480, 480, 480] else (if i.val < 62 then [] else [])))) else (if i.val < 69 then (if i.val < 66 then (if i.val < 64 then [] else (if i.val < 65 then [] else [17280, 17280, 17280])) else (if i.val < 67 then [] else (if i.val < 68 then [] else []))) else (if i.val < 72 then (if i.val < 70 then [] else (if i.val < 71 then [] else [])) else (if i.val < 74 then (if i.val < 73 then [] else [480, 480, 480, 480, 480]) else (if i.val < 75 then [] else []))))) else (if i.val < 89 then (if i.val < 82 then (if i.val < 79 then (if i.val < 77 then [] else (if i.val < 78 then [] else [])) else (if i.val < 80 then [] else (if i.val < 81 then [] else []))) else (if i.val < 85 then (if i.val < 83 then [] else (if i.val < 84 then [] else [])) else (if i.val < 87 then (if i.val < 86 then [] else []) else (if i.val < 88 then [] else [])))) else (if i.val < 95 then (if i.val < 92 then (if i.val < 90 then [] else (if i.val < 91 then [] else [])) else (if i.val < 93 then [] else (if i.val < 94 then [] else []))) else (if i.val < 98 then (if i.val < 96 then [] else (if i.val < 97 then [] else [])) else (if i.val < 100 then (if i.val < 99 then [] else []) else (if i.val < 101 then [] else [155520, 155520, 155520])))))))

theorem g32p_row34_tracePolynomial (c : Fin 102) (hc : c ∈ g32p_supplierGroup25_support) :
    g32p_supplierTracePolynomialCheck 480 (g32p_literalCentralizer c) 15
      (g32p_supplierTraceCoefficients g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) c) (g32p_literalTraceValue 33 c)
      [1, -1, 0, 1, -1, 1, 0, -1, 1] (g32p_row34_traceQuotient c) = true := by
  fin_cases c
  · exact g32p_row34_tracePolynomial_000
  · exact False.elim ((by decide : (1 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (2 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (3 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (4 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (5 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (6 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (7 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (8 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (9 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (10 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (11 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (12 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_013
  · exact False.elim ((by decide : (14 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (15 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_016
  · exact False.elim ((by decide : (17 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_018
  · exact False.elim ((by decide : (19 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (20 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (21 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_022
  · exact False.elim ((by decide : (23 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (24 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (25 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_026
  · exact False.elim ((by decide : (27 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (28 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (29 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (30 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (31 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (32 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (33 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_034
  · exact False.elim ((by decide : (35 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (36 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_037
  · exact False.elim ((by decide : (38 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (39 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (40 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (41 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (42 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (43 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (44 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (45 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (46 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_047
  · exact False.elim ((by decide : (48 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (49 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (50 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (51 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (52 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (53 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (54 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (55 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (56 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (57 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (58 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (59 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_060
  · exact False.elim ((by decide : (61 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (62 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (63 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (64 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_065
  · exact False.elim ((by decide : (66 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (67 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (68 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_069
  · exact False.elim ((by decide : (70 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (71 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (72 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_073
  · exact False.elim ((by decide : (74 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (75 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (76 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (77 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (78 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (79 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (80 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (81 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_082
  · exact False.elim ((by decide : (83 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (84 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (85 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (86 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (87 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (88 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (89 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (90 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (91 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (92 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (93 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (94 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact False.elim ((by decide : (95 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_096
  · exact g32p_row34_tracePolynomial_097
  · exact False.elim ((by decide : (98 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_099
  · exact False.elim ((by decide : (100 : Fin 102) ∉ g32p_supplierGroup25_support) hc)
  · exact g32p_row34_tracePolynomial_101

theorem g32p_row34_coinduced_literalTrace (c : Fin 102) :
    (g32p_recordedCoinduced 33 false).character (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue 33 c) := by
  by_cases hc : c ∈ g32p_supplierGroup25_support
  · have hclass (j : Fin 480) :
        IsConj (g32p_literalRepresentative c) (g32p_row34_groupEquiv j : g32p_G) ↔
          g32p_row34_supplierClassifier j = c := by
      simpa only [g32p_row34_supplierClass, Equiv.symm_apply_apply, eq_comm] using
        g32p_row34_supplierClass_iff (g32p_row34_groupEquiv j) c
    have hχ (j : Fin 480) :
        (g32p_recordedSupplierCharacters 33 (g32p_row34_groupEquiv j) : ℂ) =
          g32p_root 15 ^ (Multiplicative.toAdd (g32p_row34_characterValues j)).val := by
      rw [g32p_recordedSupplierCharacters_apply 33 (show (g32p_recordedSuppliers 33).H from g32p_row34_groupEquiv j)]
      change g32p_root 15 ^ (Multiplicative.toAdd
        (g32p_row34_characterValues (g32p_row34_groupEquiv.symm (g32p_row34_groupEquiv j)))).val = _
      rw [Equiv.symm_apply_apply]
    have h := g32p_coinduced_character_of_polynomial
      (g32p_recordedSuppliers 33).H (g32p_recordedSupplierCharacters 33)
      (g32p_literalRepresentative c) g32p_row34_groupEquiv g32p_row34_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row34_characterValues j)).val) c 15 480
      (g32p_literalCentralizer c) (g32p_literalTraceValue 33 c) [1, -1, 0, 1, -1, 1, 0, -1, 1]
      (g32p_row34_traceQuotient c) (g32p_root 15) (by decide)
      g32p_row34_finiteSupplier_order (g32p_literalCentralizer_card c) hclass hχ
      (g32p_pairing_modulus_fifteen
        (g32p_root_primitive (g32p_recordedSuppliers 33)))
      (g32p_row34_tracePolynomial c hc)
    rw [g32p_root_div_three_omega 15 (by decide)] at h
    exact h
  · exact g32p_row34_literalTrace_actual c 0 hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row34_variantArithmetic_00_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_00_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_00_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_00_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_00_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_00_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_00_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_00_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 0 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
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

theorem g32p_row34_variantArithmetic_01_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_01_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_01_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_01_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_01_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_01_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_01_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_01_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 1 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
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

theorem g32p_row34_variantArithmetic_02_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_02_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_02_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_02_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_02_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_02_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_02_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_02_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 2 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
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

theorem g32p_row34_variantArithmetic_03_0 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 0 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_03_1 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 0 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_03_2 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 1 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_03_3 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 1 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_03_4 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 2 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_03_5 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        false 3 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_03_6 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 2 := by
  decide +kernel

theorem g32p_row34_variantArithmetic_03_7 : ∀ r : Fin 16,
    let c := g32p_finBlockIndex 102 3 r
    g32p_literalTraceValue (g32p_row34_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 33 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0)
        true 3 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
