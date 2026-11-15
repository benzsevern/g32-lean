import HodgeLean.Foundations.Program.G32PropFourSixPacked0312
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow03
import HodgeLean.Foundations.Program.G32PropFourSixPacked0290
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_variantArithmetic_0 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row02_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row02_generatorIndex 0) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row02_variantArithmetic_00_0 r
  · exact g32p_row02_variantArithmetic_01_0 r
  · exact g32p_row02_variantArithmetic_02_0 r
  · exact g32p_row02_variantArithmetic_03_0 r
  · exact g32p_row02_variantArithmetic_04_0 r
  · exact g32p_row02_variantArithmetic_05_0 r
  · exact g32p_row02_variantArithmetic_06_0 r

theorem g32p_row02_variantArithmetic_1 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row02_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row02_generatorIndex 1) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 0) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row02_variantArithmetic_00_1 r
  · exact g32p_row02_variantArithmetic_01_1 r
  · exact g32p_row02_variantArithmetic_02_1 r
  · exact g32p_row02_variantArithmetic_03_1 r
  · exact g32p_row02_variantArithmetic_04_1 r
  · exact g32p_row02_variantArithmetic_05_1 r
  · exact g32p_row02_variantArithmetic_06_1 r

theorem g32p_row02_variantArithmetic_2 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row02_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row02_generatorIndex 2) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row02_variantArithmetic_00_2 r
  · exact g32p_row02_variantArithmetic_01_2 r
  · exact g32p_row02_variantArithmetic_02_2 r
  · exact g32p_row02_variantArithmetic_03_2 r
  · exact g32p_row02_variantArithmetic_04_2 r
  · exact g32p_row02_variantArithmetic_05_2 r
  · exact g32p_row02_variantArithmetic_06_2 r

theorem g32p_row02_variantArithmetic_3 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row02_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row02_generatorIndex 3) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 1) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row02_variantArithmetic_00_3 r
  · exact g32p_row02_variantArithmetic_01_3 r
  · exact g32p_row02_variantArithmetic_02_3 r
  · exact g32p_row02_variantArithmetic_03_3 r
  · exact g32p_row02_variantArithmetic_04_3 r
  · exact g32p_row02_variantArithmetic_05_3 r
  · exact g32p_row02_variantArithmetic_06_3 r

theorem g32p_row02_variantArithmetic_4 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row02_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row02_generatorIndex 4) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row02_variantArithmetic_00_4 r
  · exact g32p_row02_variantArithmetic_01_4 r
  · exact g32p_row02_variantArithmetic_02_4 r
  · exact g32p_row02_variantArithmetic_03_4 r
  · exact g32p_row02_variantArithmetic_04_4 r
  · exact g32p_row02_variantArithmetic_05_4 r
  · exact g32p_row02_variantArithmetic_06_4 r

theorem g32p_row02_variantArithmetic_5 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row02_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row02_generatorIndex 5) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) false 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row02_variantArithmetic_00_5 r
  · exact g32p_row02_variantArithmetic_01_5 r
  · exact g32p_row02_variantArithmetic_02_5 r
  · exact g32p_row02_variantArithmetic_03_5 r
  · exact g32p_row02_variantArithmetic_04_5 r
  · exact g32p_row02_variantArithmetic_05_5 r
  · exact g32p_row02_variantArithmetic_06_5 r

theorem g32p_row02_variantArithmetic_6 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row02_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row02_generatorIndex 6) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 2) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row02_variantArithmetic_00_6 r
  · exact g32p_row02_variantArithmetic_01_6 r
  · exact g32p_row02_variantArithmetic_02_6 r
  · exact g32p_row02_variantArithmetic_03_6 r
  · exact g32p_row02_variantArithmetic_04_6 r
  · exact g32p_row02_variantArithmetic_05_6 r
  · exact g32p_row02_variantArithmetic_06_6 r

theorem g32p_row02_variantArithmetic_7 (c : Fin 102) :
    g32p_literalTraceValue (g32p_row02_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3 := by
  apply g32p_forall_fin_blocks (fun c =>
    g32p_literalTraceValue (g32p_row02_generatorIndex 7) c =
      g32p_supplierVariantTracePair (g32p_literalTraceValue 1 c)
        (g32p_literalDeterminantPair c) (g32p_literalPowerTrace c 0) true 3) ?_ c
  intro q r
  fin_cases q
  · exact g32p_row02_variantArithmetic_00_7 r
  · exact g32p_row02_variantArithmetic_01_7 r
  · exact g32p_row02_variantArithmetic_02_7 r
  · exact g32p_row02_variantArithmetic_03_7 r
  · exact g32p_row02_variantArithmetic_04_7 r
  · exact g32p_row02_variantArithmetic_05_7 r
  · exact g32p_row02_variantArithmetic_06_7 r

theorem g32p_row02_all_literalTrace_actual (c : Fin 102) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row02_generatorIndex k)).character
        (g32p_literalRepresentative c) =
      HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue (g32p_row02_generatorIndex k) c) := by
  fin_cases k
  · exact (g32p_supplierVariantTrace_actual 1 c _ (g32p_row02_coinduced_literalTrace c)
      false 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row02_variantArithmetic_0 c).symm)
  · exact (g32p_supplierVariantTrace_actual 1 c _ (g32p_row02_coinduced_literalTrace c)
      true 0).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row02_variantArithmetic_1 c).symm)
  · exact (g32p_supplierVariantTrace_actual 1 c _ (g32p_row02_coinduced_literalTrace c)
      false 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row02_variantArithmetic_2 c).symm)
  · exact (g32p_supplierVariantTrace_actual 1 c _ (g32p_row02_coinduced_literalTrace c)
      true 1).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row02_variantArithmetic_3 c).symm)
  · exact (g32p_supplierVariantTrace_actual 1 c _ (g32p_row02_coinduced_literalTrace c)
      false 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row02_variantArithmetic_4 c).symm)
  · exact (g32p_supplierVariantTrace_actual 1 c _ (g32p_row02_coinduced_literalTrace c)
      false 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row02_variantArithmetic_5 c).symm)
  · exact (g32p_supplierVariantTrace_actual 1 c _ (g32p_row02_coinduced_literalTrace c)
      true 2).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row02_variantArithmetic_6 c).symm)
  · exact (g32p_supplierVariantTrace_actual 1 c _ (g32p_row02_coinduced_literalTrace c)
      true 3).trans
        (congrArg (HurwitzPrymRex_ev g32h_omega) (g32p_row02_variantArithmetic_7 c).symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierGroup01_source : Fin 4320 → Fin 145 × Fin 256 :=
  fun i => (if i.val < 2160 then (if i.val < 1080 then (if i.val < 540 then (if i.val < 270 then (if i.val < 135 then (if i.val < 67 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then (0, 0) else (107, 81)) else (if i.val < 3 then (71, 200) else (22, 54))) else (if i.val < 6 then (if i.val < 5 then (88, 152) else (34, 52)) else (if i.val < 7 then (78, 192) else (143, 41)))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then (137, 41) else (120, 202)) else (if i.val < 11 then (116, 196) else (114, 46))) else (if i.val < 14 then (if i.val < 13 then (80, 57) else (77, 152)) else (if i.val < 15 then (66, 129) else (0, 99))))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then (114, 22) else (85, 142)) else (if i.val < 19 then (51, 130) else (85, 128))) else (if i.val < 22 then (if i.val < 21 then (104, 103) else (80, 80)) else (if i.val < 23 then (120, 107) else (58, 75)))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then (13, 32) else (48, 254)) else (if i.val < 27 then (120, 145) else (28, 232))) else (if i.val < 30 then (if i.val < 29 then (135, 132) else (39, 189)) else (if i.val < 31 then (0, 97) else (if i.val < 32 then (140, 241) else (143, 208))))))) else (if i.val < 50 then (if i.val < 41 then (if i.val < 37 then (if i.val < 35 then (if i.val < 34 then (97, 11) else (126, 138)) else (if i.val < 36 then (120, 214) else (63, 217))) else (if i.val < 39 then (if i.val < 38 then (140, 8) else (129, 182)) else (if i.val < 40 then (111, 1) else (115, 35)))) else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then (79, 191) else (142, 234)) else (if i.val < 44 then (104, 245) else (135, 1))) else (if i.val < 47 then (if i.val < 46 then (140, 216) else (136, 170)) else (if i.val < 48 then (62, 47) else (if i.val < 49 then (77, 219) else (118, 178)))))) else (if i.val < 58 then (if i.val < 54 then (if i.val < 52 then (if i.val < 51 then (134, 3) else (136, 38)) else (if i.val < 53 then (143, 50) else (143, 143))) else (if i.val < 56 then (if i.val < 55 then (91, 252) else (144, 174)) else (if i.val < 57 then (81, 208) else (122, 19)))) else (if i.val < 62 then (if i.val < 60 then (if i.val < 59 then (21, 159) else (74, 222)) else (if i.val < 61 then (133, 101) else (66, 85))) else (if i.val < 64 then (if i.val < 63 then (137, 88) else (101, 187)) else (if i.val < 65 then (2, 119) else (if i.val < 66 then (122, 250) else (51, 68)))))))) else (if i.val < 101 then (if i.val < 84 then (if i.val < 75 then (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then (36, 59) else (141, 11)) else (if i.val < 70 then (122, 54) else (3, 223))) else (if i.val < 73 then (if i.val < 72 then (124, 245) else (53, 5)) else (if i.val < 74 then (76, 84) else (135, 105)))) else (if i.val < 79 then (if i.val < 77 then (if i.val < 76 then (109, 182) else (5, 205)) else (if i.val < 78 then (126, 106) else (15, 122))) else (if i.val < 81 then (if i.val < 80 then (140, 139) else (139, 26)) else (if i.val < 82 then (39, 55) else (if i.val < 83 then (141, 25) else (46, 85)))))) else (if i.val < 92 then (if i.val < 88 then (if i.val < 86 then (if i.val < 85 then (35, 197) else (142, 242)) else (if i.val < 87 then (109, 21) else (87, 165))) else (if i.val < 90 then (if i.val < 89 then (129, 61) else (130, 181)) else (if i.val < 91 then (126, 207) else (139, 125)))) else (if i.val < 96 then (if i.val < 94 then (if i.val < 93 then (108, 220) else (19, 41)) else (if i.val < 95 then (82, 106) else (95, 133))) else (if i.val < 98 then (if i.val < 97 then (34, 124) else (104, 0)) else (if i.val < 99 then (141, 51) else (if i.val < 100 then (142, 245) else (12, 68))))))) else (if i.val < 118 then (if i.val < 109 then (if i.val < 105 then (if i.val < 103 then (if i.val < 102 then (23, 200) else (0, 56)) else (if i.val < 104 then (30, 200) else (140, 74))) else (if i.val < 107 then (if i.val < 106 then (144, 111) else (129, 106)) else (if i.val < 108 then (59, 24) else (141, 18)))) else (if i.val < 113 then (if i.val < 111 then (if i.val < 110 then (74, 144) else (113, 219)) else (if i.val < 112 then (125, 105) else (129, 207))) else (if i.val < 115 then (if i.val < 114 then (16, 238) else (46, 149)) else (if i.val < 116 then (139, 93) else (if i.val < 117 then (65, 77) else (119, 80)))))) else (if i.val < 126 then (if i.val < 122 then (if i.val < 120 then (if i.val < 119 then (142, 75) else (123, 95)) else (if i.val < 121 then (49, 188) else (143, 169))) else (if i.val < 124 then (if i.val < 123 then (144, 89) else (9, 43)) else (if i.val < 125 then (119, 26) else (97, 172)))) else (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then (105, 71) else (90, 175)) else (if i.val < 129 then (109, 142) else (62, 147))) else (if i.val < 132 then (if i.val < 131 then (141, 255) else (140, 202)) else (if i.val < 133 then (137, 214) else (if i.val < 134 then (133, 33) else (38, 107))))))))) else (if i.val < 202 then (if i.val < 168 then (if i.val < 151 then (if i.val < 143 then (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then (143, 85) else (106, 37)) else (if i.val < 138 then (140, 167) else (129, 126))) else (if i.val < 141 then (if i.val < 140 then (113, 216) else (104, 205)) else (if i.val < 142 then (86, 208) else (143, 25)))) else (if i.val < 147 then (if i.val < 145 then (if i.val < 144 then (102, 37) else (119, 223)) else (if i.val < 146 then (110, 106) else (38, 246))) else (if i.val < 149 then (if i.val < 148 then (103, 95) else (112, 181)) else (if i.val < 150 then (57, 42) else (86, 179))))) else (if i.val < 159 then (if i.val < 155 then (if i.val < 153 then (if i.val < 152 then (136, 106) else (110, 175)) else (if i.val < 154 then (90, 251) else (93, 204))) else (if i.val < 157 then (if i.val < 156 then (143, 210) else (130, 11)) else (if i.val < 158 then (141, 97) else (88, 33)))) else (if i.val < 163 then (if i.val < 161 then (if i.val < 160 then (75, 216) else (141, 83)) else (if i.val < 162 then (132, 7) else (26, 44))) else (if i.val < 165 then (if i.val < 164 then (136, 90) else (34, 16)) else (if i.val < 166 then (121, 188) else (if i.val < 167 then (79, 32) else (132, 23))))))) else (if i.val < 185 then (if i.val < 176 then (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then (113, 173) else (110, 235)) else (if i.val < 171 then (103, 118) else (95, 235))) else (if i.val < 174 then (if i.val < 173 then (131, 114) else (141, 17)) else (if i.val < 175 then (64, 165) else (137, 223)))) else (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then (20, 48) else (135, 10)) else (if i.val < 179 then (24, 8) else (92, 212))) else (if i.val < 182 then (if i.val < 181 then (144, 12) else (72, 121)) else (if i.val < 183 then (127, 166) else (if i.val < 184 then (86, 234) else (140, 121)))))) else (if i.val < 193 then (if i.val < 189 then (if i.val < 187 then (if i.val < 186 then (31, 58) else (113, 28)) else (if i.val < 188 then (124, 143) else (137, 224))) else (if i.val < 191 then (if i.val < 190 then (142, 134) else (83, 5)) else (if i.val < 192 then (121, 56) else (142, 72)))) else (if i.val < 197 then (if i.val < 195 then (if i.val < 194 then (52, 4) else (58, 166)) else (if i.val < 196 then (49, 233) else (130, 77))) else (if i.val < 199 then (if i.val < 198 then (141, 32) else (121, 199)) else (if i.val < 200 then (140, 144) else (if i.val < 201 then (32, 24) else (137, 185)))))))) else (if i.val < 236 then (if i.val < 219 then (if i.val < 210 then (if i.val < 206 then (if i.val < 204 then (if i.val < 203 then (106, 121) else (135, 243)) else (if i.val < 205 then (110, 231) else (120, 197))) else (if i.val < 208 then (if i.val < 207 then (63, 222) else (122, 140)) else (if i.val < 209 then (37, 110) else (36, 87)))) else (if i.val < 214 then (if i.val < 212 then (if i.val < 211 then (108, 145) else (136, 154)) else (if i.val < 213 then (114, 27) else (133, 165))) else (if i.val < 216 then (if i.val < 215 then (110, 238) else (140, 61)) else (if i.val < 217 then (20, 199) else (if i.val < 218 then (92, 148) else (46, 125)))))) else (if i.val < 227 then (if i.val < 223 then (if i.val < 221 then (if i.val < 220 then (31, 46) else (55, 14)) else (if i.val < 222 then (32, 125) else (111, 26))) else (if i.val < 225 then (if i.val < 224 then (35, 234) else (85, 179)) else (if i.val < 226 then (109, 104) else (110, 218)))) else (if i.val < 231 then (if i.val < 229 then (if i.val < 228 then (76, 102) else (63, 240)) else (if i.val < 230 then (120, 77) else (32, 91))) else (if i.val < 233 then (if i.val < 232 then (118, 226) else (53, 46)) else (if i.val < 234 then (0, 96) else (if i.val < 235 then (79, 183) else (38, 30))))))) else (if i.val < 253 then (if i.val < 244 then (if i.val < 240 then (if i.val < 238 then (if i.val < 237 then (142, 226) else (76, 187)) else (if i.val < 239 then (118, 189) else (41, 98))) else (if i.val < 242 then (if i.val < 241 then (98, 6) else (6, 150)) else (if i.val < 243 then (142, 247) else (53, 76)))) else (if i.val < 248 then (if i.val < 246 then (if i.val < 245 then (124, 76) else (129, 196)) else (if i.val < 247 then (74, 111) else (60, 66))) else (if i.val < 250 then (if i.val < 249 then (63, 246) else (128, 166)) else (if i.val < 251 then (56, 244) else (if i.val < 252 then (53, 144) else (141, 79)))))) else (if i.val < 261 then (if i.val < 257 then (if i.val < 255 then (if i.val < 254 then (74, 132) else (50, 174)) else (if i.val < 256 then (120, 30) else (137, 6))) else (if i.val < 259 then (if i.val < 258 then (129, 117) else (46, 189)) else (if i.val < 260 then (113, 234) else (19, 207)))) else (if i.val < 265 then (if i.val < 263 then (if i.val < 262 then (143, 44) else (67, 80)) else (if i.val < 264 then (48, 6) else (54, 144))) else (if i.val < 267 then (if i.val < 266 then (7, 223) else (124, 146)) else (if i.val < 268 then (139, 153) else (if i.val < 269 then (53, 24) else (84, 73)))))))))) else (if i.val < 405 then (if i.val < 337 then (if i.val < 303 then (if i.val < 286 then (if i.val < 278 then (if i.val < 274 then (if i.val < 272 then (if i.val < 271 then (142, 98) else (138, 244)) else (if i.val < 273 then (30, 162) else (90, 110))) else (if i.val < 276 then (if i.val < 275 then (129, 123) else (119, 118)) else (if i.val < 277 then (136, 179) else (18, 207)))) else (if i.val < 282 then (if i.val < 280 then (if i.val < 279 then (81, 92) else (47, 198)) else (if i.val < 281 then (143, 100) else (136, 167))) else (if i.val < 284 then (if i.val < 283 then (45, 137) else (133, 244)) else (if i.val < 285 then (117, 102) else (130, 54))))) else (if i.val < 294 then (if i.val < 290 then (if i.val < 288 then (if i.val < 287 then (124, 40) else (138, 128)) else (if i.val < 289 then (125, 150) else (141, 89))) else (if i.val < 292 then (if i.val < 291 then (114, 20) else (87, 128)) else (if i.val < 293 then (56, 242) else (33, 157)))) else (if i.val < 298 then (if i.val < 296 then (if i.val < 295 then (111, 206) else (40, 136)) else (if i.val < 297 then (64, 171) else (132, 236))) else (if i.val < 300 then (if i.val < 299 then (109, 199) else (58, 72)) else (if i.val < 301 then (87, 158) else (if i.val < 302 then (106, 199) else (68, 194))))))) else (if i.val < 320 then (if i.val < 311 then (if i.val < 307 then (if i.val < 305 then (if i.val < 304 then (75, 48) else (99, 192)) else (if i.val < 306 then (63, 27) else (122, 211))) else (if i.val < 309 then (if i.val < 308 then (8, 183) else (124, 214)) else (if i.val < 310 then (11, 51) else (144, 219)))) else (if i.val < 315 then (if i.val < 313 then (if i.val < 312 then (73, 24) else (125, 143)) else (if i.val < 314 then (132, 250) else (107, 67))) else (if i.val < 317 then (if i.val < 316 then (126, 143) else (57, 243)) else (if i.val < 318 then (87, 43) else (if i.val < 319 then (28, 255) else (58, 61)))))) else (if i.val < 328 then (if i.val < 324 then (if i.val < 322 then (if i.val < 321 then (119, 107) else (122, 2)) else (if i.val < 323 then (68, 108) else (110, 219))) else (if i.val < 326 then (if i.val < 325 then (121, 10) else (115, 61)) else (if i.val < 327 then (132, 89) else (120, 178)))) else (if i.val < 332 then (if i.val < 330 then (if i.val < 329 then (137, 111) else (74, 240)) else (if i.val < 331 then (76, 89) else (40, 124))) else (if i.val < 334 then (if i.val < 333 then (84, 74) else (114, 79)) else (if i.val < 335 then (142, 104) else (if i.val < 336 then (84, 37) else (116, 107)))))))) else (if i.val < 371 then (if i.val < 354 then (if i.val < 345 then (if i.val < 341 then (if i.val < 339 then (if i.val < 338 then (14, 221) else (81, 48)) else (if i.val < 340 then (143, 127) else (129, 220))) else (if i.val < 343 then (if i.val < 342 then (8, 73) else (87, 131)) else (if i.val < 344 then (114, 222) else (23, 63)))) else (if i.val < 349 then (if i.val < 347 then (if i.val < 346 then (46, 38) else (128, 18)) else (if i.val < 348 then (142, 47) else (133, 41))) else (if i.val < 351 then (if i.val < 350 then (107, 54) else (66, 161)) else (if i.val < 352 then (141, 125) else (if i.val < 353 then (11, 198) else (116, 75)))))) else (if i.val < 362 then (if i.val < 358 then (if i.val < 356 then (if i.val < 355 then (24, 100) else (8, 199)) else (if i.val < 357 then (133, 42) else (31, 181))) else (if i.val < 360 then (if i.val < 359 then (121, 163) else (91, 222)) else (if i.val < 361 then (131, 119) else (64, 213)))) else (if i.val < 366 then (if i.val < 364 then (if i.val < 363 then (16, 184) else (144, 122)) else (if i.val < 365 then (45, 221) else (113, 118))) else (if i.val < 368 then (if i.val < 367 then (89, 70) else (118, 64)) else (if i.val < 369 then (121, 83) else (if i.val < 370 then (89, 203) else (43, 132))))))) else (if i.val < 388 then (if i.val < 379 then (if i.val < 375 then (if i.val < 373 then (if i.val < 372 then (134, 44) else (104, 188)) else (if i.val < 374 then (5, 107) else (74, 109))) else (if i.val < 377 then (if i.val < 376 then (46, 199) else (133, 181)) else (if i.val < 378 then (23, 241) else (79, 71)))) else (if i.val < 383 then (if i.val < 381 then (if i.val < 380 then (116, 138) else (29, 171)) else (if i.val < 382 then (100, 146) else (142, 103))) else (if i.val < 385 then (if i.val < 384 then (112, 90) else (14, 222)) else (if i.val < 386 then (139, 18) else (if i.val < 387 then (93, 111) else (132, 197)))))) else (if i.val < 396 then (if i.val < 392 then (if i.val < 390 then (if i.val < 389 then (98, 212) else (116, 33)) else (if i.val < 391 then (99, 148) else (60, 142))) else (if i.val < 394 then (if i.val < 393 then (127, 151) else (22, 146)) else (if i.val < 395 then (71, 67) else (126, 99)))) else (if i.val < 400 then (if i.val < 398 then (if i.val < 397 then (139, 49) else (52, 153)) else (if i.val < 399 then (138, 201) else (56, 137))) else (if i.val < 402 then (if i.val < 401 then (16, 76) else (34, 108)) else (if i.val < 403 then (0, 101) else (if i.val < 404 then (111, 113) else (115, 170))))))))) else (if i.val < 472 then (if i.val < 438 then (if i.val < 421 then (if i.val < 413 then (if i.val < 409 then (if i.val < 407 then (if i.val < 406 then (100, 87) else (62, 121)) else (if i.val < 408 then (138, 196) else (118, 116))) else (if i.val < 411 then (if i.val < 410 then (121, 3) else (139, 36)) else (if i.val < 412 then (107, 34) else (144, 135)))) else (if i.val < 417 then (if i.val < 415 then (if i.val < 414 then (104, 229) else (68, 127)) else (if i.val < 416 then (140, 227) else (143, 194))) else (if i.val < 419 then (if i.val < 418 then (133, 169) else (89, 151)) else (if i.val < 420 then (112, 239) else (92, 1))))) else (if i.val < 429 then (if i.val < 425 then (if i.val < 423 then (if i.val < 422 then (143, 23) else (119, 110)) else (if i.val < 424 then (122, 43) else (125, 84))) else (if i.val < 427 then (if i.val < 426 then (117, 53) else (135, 109)) else (if i.val < 428 then (137, 25) else (29, 194)))) else (if i.val < 433 then (if i.val < 431 then (if i.val < 430 then (136, 234) else (133, 243)) else (if i.val < 432 then (133, 106) else (69, 21))) else (if i.val < 435 then (if i.val < 434 then (133, 201) else (130, 99)) else (if i.val < 436 then (143, 4) else (if i.val < 437 then (113, 50) else (139, 122))))))) else (if i.val < 455 then (if i.val < 446 then (if i.val < 442 then (if i.val < 440 then (if i.val < 439 then (132, 27) else (102, 77)) else (if i.val < 441 then (119, 21) else (102, 38))) else (if i.val < 444 then (if i.val < 443 then (136, 157) else (61, 87)) else (if i.val < 445 then (1, 72) else (120, 106)))) else (if i.val < 450 then (if i.val < 448 then (if i.val < 447 then (46, 211) else (118, 20)) else (if i.val < 449 then (34, 185) else (138, 8))) else (if i.val < 452 then (if i.val < 451 then (28, 147) else (138, 166)) else (if i.val < 453 then (72, 0) else (if i.val < 454 then (112, 47) else (129, 76)))))) else (if i.val < 463 then (if i.val < 459 then (if i.val < 457 then (if i.val < 456 then (76, 14) else (93, 168)) else (if i.val < 458 then (131, 78) else (76, 188))) else (if i.val < 461 then (if i.val < 460 then (108, 107) else (24, 171)) else (if i.val < 462 then (93, 179) else (123, 144)))) else (if i.val < 467 then (if i.val < 465 then (if i.val < 464 then (69, 227) else (89, 145)) else (if i.val < 466 then (119, 28) else (134, 237))) else (if i.val < 469 then (if i.val < 468 then (122, 111) else (31, 86)) else (if i.val < 470 then (134, 13) else (if i.val < 471 then (144, 139) else (58, 157)))))))) else (if i.val < 506 then (if i.val < 489 then (if i.val < 480 then (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then (48, 3) else (107, 3)) else (if i.val < 475 then (138, 47) else (115, 187))) else (if i.val < 478 then (if i.val < 477 then (119, 190) else (53, 103)) else (if i.val < 479 then (73, 25) else (119, 182)))) else (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then (100, 216) else (72, 253)) else (if i.val < 483 then (36, 0) else (119, 115))) else (if i.val < 486 then (if i.val < 485 then (55, 52) else (58, 181)) else (if i.val < 487 then (37, 198) else (if i.val < 488 then (100, 221) else (19, 168)))))) else (if i.val < 497 then (if i.val < 493 then (if i.val < 491 then (if i.val < 490 then (106, 170) else (119, 24)) else (if i.val < 492 then (132, 151) else (110, 222))) else (if i.val < 495 then (if i.val < 494 then (142, 189) else (141, 110)) else (if i.val < 496 then (107, 56) else (115, 236)))) else (if i.val < 501 then (if i.val < 499 then (if i.val < 498 then (57, 151) else (137, 252)) else (if i.val < 500 then (91, 6) else (117, 130))) else (if i.val < 503 then (if i.val < 502 then (107, 129) else (45, 138)) else (if i.val < 504 then (39, 168) else (if i.val < 505 then (112, 24) else (131, 60))))))) else (if i.val < 523 then (if i.val < 514 then (if i.val < 510 then (if i.val < 508 then (if i.val < 507 then (125, 148) else (119, 144)) else (if i.val < 509 then (108, 252) else (143, 142))) else (if i.val < 512 then (if i.val < 511 then (59, 21) else (115, 34)) else (if i.val < 513 then (94, 188) else (137, 71)))) else (if i.val < 518 then (if i.val < 516 then (if i.val < 515 then (5, 168) else (62, 234)) else (if i.val < 517 then (141, 215) else (78, 215))) else (if i.val < 520 then (if i.val < 519 then (113, 36) else (136, 12)) else (if i.val < 521 then (85, 140) else (if i.val < 522 then (143, 74) else (133, 5)))))) else (if i.val < 531 then (if i.val < 527 then (if i.val < 525 then (if i.val < 524 then (138, 45) else (52, 62)) else (if i.val < 526 then (31, 59) else (116, 145))) else (if i.val < 529 then (if i.val < 528 then (115, 183) else (140, 120)) else (if i.val < 530 then (75, 126) else (121, 19)))) else (if i.val < 535 then (if i.val < 533 then (if i.val < 532 then (8, 214) else (34, 248)) else (if i.val < 534 then (127, 89) else (50, 159))) else (if i.val < 537 then (if i.val < 536 then (129, 7) else (137, 201)) else (if i.val < 538 then (36, 196) else (if i.val < 539 then (109, 217) else (70, 31))))))))))) else (if i.val < 810 then (if i.val < 675 then (if i.val < 607 then (if i.val < 573 then (if i.val < 556 then (if i.val < 548 then (if i.val < 544 then (if i.val < 542 then (if i.val < 541 then (54, 18) else (83, 151)) else (if i.val < 543 then (138, 90) else (115, 28))) else (if i.val < 546 then (if i.val < 545 then (134, 207) else (73, 114)) else (if i.val < 547 then (28, 124) else (71, 153)))) else (if i.val < 552 then (if i.val < 550 then (if i.val < 549 then (49, 204) else (127, 185)) else (if i.val < 551 then (143, 83) else (34, 135))) else (if i.val < 554 then (if i.val < 553 then (30, 234) else (77, 227)) else (if i.val < 555 then (100, 66) else (133, 253))))) else (if i.val < 564 then (if i.val < 560 then (if i.val < 558 then (if i.val < 557 then (37, 152) else (134, 230)) else (if i.val < 559 then (101, 82) else (84, 254))) else (if i.val < 562 then (if i.val < 561 then (61, 228) else (66, 99)) else (if i.val < 563 then (127, 54) else (95, 145)))) else (if i.val < 568 then (if i.val < 566 then (if i.val < 565 then (143, 219) else (120, 232)) else (if i.val < 567 then (144, 59) else (131, 18))) else (if i.val < 570 then (if i.val < 569 then (91, 16) else (142, 187)) else (if i.val < 571 then (96, 53) else (if i.val < 572 then (122, 123) else (139, 119))))))) else (if i.val < 590 then (if i.val < 581 then (if i.val < 577 then (if i.val < 575 then (if i.val < 574 then (127, 253) else (94, 35)) else (if i.val < 576 then (134, 61) else (119, 17))) else (if i.val < 579 then (if i.val < 578 then (117, 126) else (99, 235)) else (if i.val < 580 then (79, 27) else (21, 123)))) else (if i.val < 585 then (if i.val < 583 then (if i.val < 582 then (128, 140) else (60, 7)) else (if i.val < 584 then (57, 185) else (74, 189))) else (if i.val < 587 then (if i.val < 586 then (116, 3) else (42, 20)) else (if i.val < 588 then (44, 77) else (if i.val < 589 then (132, 106) else (144, 75)))))) else (if i.val < 598 then (if i.val < 594 then (if i.val < 592 then (if i.val < 591 then (123, 129) else (116, 184)) else (if i.val < 593 then (117, 15) else (136, 1))) else (if i.val < 596 then (if i.val < 595 then (84, 34) else (109, 146)) else (if i.val < 597 then (121, 68) else (88, 193)))) else (if i.val < 602 then (if i.val < 600 then (if i.val < 599 then (71, 2) else (89, 176)) else (if i.val < 601 then (143, 103) else (138, 18))) else (if i.val < 604 then (if i.val < 603 then (121, 170) else (134, 47)) else (if i.val < 605 then (131, 46) else (if i.val < 606 then (38, 103) else (19, 23)))))))) else (if i.val < 641 then (if i.val < 624 then (if i.val < 615 then (if i.val < 611 then (if i.val < 609 then (if i.val < 608 then (128, 109) else (112, 3)) else (if i.val < 610 then (126, 95) else (106, 230))) else (if i.val < 613 then (if i.val < 612 then (142, 15) else (137, 173)) else (if i.val < 614 then (129, 144) else (73, 212)))) else (if i.val < 619 then (if i.val < 617 then (if i.val < 616 then (112, 28) else (115, 211)) else (if i.val < 618 then (143, 37) else (143, 145))) else (if i.val < 621 then (if i.val < 620 then (133, 112) else (133, 9)) else (if i.val < 622 then (88, 205) else (if i.val < 623 then (78, 226) else (68, 73)))))) else (if i.val < 632 then (if i.val < 628 then (if i.val < 626 then (if i.val < 625 then (85, 124) else (99, 121)) else (if i.val < 627 then (140, 7) else (103, 236))) else (if i.val < 630 then (if i.val < 629 then (21, 173) else (84, 71)) else (if i.val < 631 then (38, 169) else (134, 86)))) else (if i.val < 636 then (if i.val < 634 then (if i.val < 633 then (109, 36) else (102, 2)) else (if i.val < 635 then (124, 179) else (131, 215))) else (if i.val < 638 then (if i.val < 637 then (8, 24) else (61, 69)) else (if i.val < 639 then (36, 50) else (if i.val < 640 then (96, 120) else (72, 173))))))) else (if i.val < 658 then (if i.val < 649 then (if i.val < 645 then (if i.val < 643 then (if i.val < 642 then (62, 71) else (116, 100)) else (if i.val < 644 then (136, 99) else (28, 6))) else (if i.val < 647 then (if i.val < 646 then (53, 160) else (143, 200)) else (if i.val < 648 then (133, 102) else (141, 216)))) else (if i.val < 653 then (if i.val < 651 then (if i.val < 650 then (140, 105) else (104, 160)) else (if i.val < 652 then (82, 155) else (11, 182))) else (if i.val < 655 then (if i.val < 654 then (139, 21) else (10, 161)) else (if i.val < 656 then (112, 21) else (if i.val < 657 then (131, 32) else (75, 205)))))) else (if i.val < 666 then (if i.val < 662 then (if i.val < 660 then (if i.val < 659 then (98, 193) else (38, 120)) else (if i.val < 661 then (89, 193) else (135, 31))) else (if i.val < 664 then (if i.val < 663 then (99, 211) else (137, 183)) else (if i.val < 665 then (131, 227) else (61, 104)))) else (if i.val < 670 then (if i.val < 668 then (if i.val < 667 then (131, 155) else (121, 200)) else (if i.val < 669 then (125, 71) else (105, 89))) else (if i.val < 672 then (if i.val < 671 then (117, 253) else (127, 159)) else (if i.val < 673 then (39, 37) else (if i.val < 674 then (142, 83) else (45, 191))))))))) else (if i.val < 742 then (if i.val < 708 then (if i.val < 691 then (if i.val < 683 then (if i.val < 679 then (if i.val < 677 then (if i.val < 676 then (133, 140) else (110, 37)) else (if i.val < 678 then (125, 186) else (62, 247))) else (if i.val < 681 then (if i.val < 680 then (132, 28) else (35, 59)) else (if i.val < 682 then (19, 88) else (143, 79)))) else (if i.val < 687 then (if i.val < 685 then (if i.val < 684 then (78, 30) else (143, 57)) else (if i.val < 686 then (128, 187) else (143, 248))) else (if i.val < 689 then (if i.val < 688 then (114, 176) else (106, 210)) else (if i.val < 690 then (135, 213) else (61, 192))))) else (if i.val < 699 then (if i.val < 695 then (if i.val < 693 then (if i.val < 692 then (118, 23) else (109, 228)) else (if i.val < 694 then (123, 84) else (78, 216))) else (if i.val < 697 then (if i.val < 696 then (134, 210) else (19, 210)) else (if i.val < 698 then (88, 41) else (142, 214)))) else (if i.val < 703 then (if i.val < 701 then (if i.val < 700 then (104, 40) else (82, 28)) else (if i.val < 702 then (75, 85) else (61, 54))) else (if i.val < 705 then (if i.val < 704 then (141, 7) else (115, 175)) else (if i.val < 706 then (119, 168) else (if i.val < 707 then (135, 219) else (143, 140))))))) else (if i.val < 725 then (if i.val < 716 then (if i.val < 712 then (if i.val < 710 then (if i.val < 709 then (127, 243) else (111, 251)) else (if i.val < 711 then (127, 214) else (81, 29))) else (if i.val < 714 then (if i.val < 713 then (94, 46) else (123, 214)) else (if i.val < 715 then (89, 255) else (40, 90)))) else (if i.val < 720 then (if i.val < 718 then (if i.val < 717 then (136, 30) else (143, 238)) else (if i.val < 719 then (129, 224) else (99, 197))) else (if i.val < 722 then (if i.val < 721 then (144, 34) else (144, 227)) else (if i.val < 723 then (113, 68) else (if i.val < 724 then (134, 76) else (79, 208)))))) else (if i.val < 733 then (if i.val < 729 then (if i.val < 727 then (if i.val < 726 then (132, 168) else (78, 172)) else (if i.val < 728 then (104, 87) else (135, 39))) else (if i.val < 731 then (if i.val < 730 then (28, 104) else (131, 241)) else (if i.val < 732 then (22, 219) else (111, 90)))) else (if i.val < 737 then (if i.val < 735 then (if i.val < 734 then (138, 236) else (104, 175)) else (if i.val < 736 then (118, 98) else (48, 100))) else (if i.val < 739 then (if i.val < 738 then (97, 249) else (80, 19)) else (if i.val < 740 then (135, 142) else (if i.val < 741 then (57, 89) else (55, 103)))))))) else (if i.val < 776 then (if i.val < 759 then (if i.val < 750 then (if i.val < 746 then (if i.val < 744 then (if i.val < 743 then (135, 6) else (113, 235)) else (if i.val < 745 then (142, 118) else (140, 11))) else (if i.val < 748 then (if i.val < 747 then (92, 46) else (51, 91)) else (if i.val < 749 then (86, 171) else (64, 62)))) else (if i.val < 754 then (if i.val < 752 then (if i.val < 751 then (72, 176) else (9, 137)) else (if i.val < 753 then (131, 243) else (72, 170))) else (if i.val < 756 then (if i.val < 755 then (112, 125) else (131, 91)) else (if i.val < 757 then (88, 45) else (if i.val < 758 then (133, 203) else (144, 204)))))) else (if i.val < 767 then (if i.val < 763 then (if i.val < 761 then (if i.val < 760 then (117, 97) else (18, 2)) else (if i.val < 762 then (95, 30) else (70, 235))) else (if i.val < 765 then (if i.val < 764 then (55, 164) else (116, 34)) else (if i.val < 766 then (48, 63) else (26, 79)))) else (if i.val < 771 then (if i.val < 769 then (if i.val < 768 then (115, 222) else (23, 188)) else (if i.val < 770 then (82, 203) else (45, 146))) else (if i.val < 773 then (if i.val < 772 then (78, 202) else (131, 165)) else (if i.val < 774 then (141, 151) else (if i.val < 775 then (136, 50) else (72, 43))))))) else (if i.val < 793 then (if i.val < 784 then (if i.val < 780 then (if i.val < 778 then (if i.val < 777 then (116, 29) else (109, 106)) else (if i.val < 779 then (92, 96) else (123, 151))) else (if i.val < 782 then (if i.val < 781 then (71, 239) else (50, 228)) else (if i.val < 783 then (142, 239) else (48, 11)))) else (if i.val < 788 then (if i.val < 786 then (if i.val < 785 then (139, 117) else (132, 111)) else (if i.val < 787 then (131, 94) else (144, 133))) else (if i.val < 790 then (if i.val < 789 then (69, 6) else (46, 177)) else (if i.val < 791 then (144, 105) else (if i.val < 792 then (60, 14) else (2, 35)))))) else (if i.val < 801 then (if i.val < 797 then (if i.val < 795 then (if i.val < 794 then (90, 187) else (130, 207)) else (if i.val < 796 then (55, 84) else (32, 127))) else (if i.val < 799 then (if i.val < 798 then (55, 17) else (127, 207)) else (if i.val < 800 then (117, 13) else (5, 105)))) else (if i.val < 805 then (if i.val < 803 then (if i.val < 802 then (102, 103) else (89, 10)) else (if i.val < 804 then (46, 145) else (127, 138))) else (if i.val < 807 then (if i.val < 806 then (108, 129) else (122, 69)) else (if i.val < 808 then (133, 81) else (if i.val < 809 then (136, 88) else (53, 197)))))))))) else (if i.val < 945 then (if i.val < 877 then (if i.val < 843 then (if i.val < 826 then (if i.val < 818 then (if i.val < 814 then (if i.val < 812 then (if i.val < 811 then (113, 65) else (121, 124)) else (if i.val < 813 then (133, 185) else (143, 10))) else (if i.val < 816 then (if i.val < 815 then (117, 186) else (4, 217)) else (if i.val < 817 then (110, 55) else (114, 160)))) else (if i.val < 822 then (if i.val < 820 then (if i.val < 819 then (107, 218) else (7, 103)) else (if i.val < 821 then (136, 238) else (9, 18))) else (if i.val < 824 then (if i.val < 823 then (69, 109) else (144, 78)) else (if i.val < 825 then (29, 82) else (40, 140))))) else (if i.val < 834 then (if i.val < 830 then (if i.val < 828 then (if i.val < 827 then (121, 65) else (42, 243)) else (if i.val < 829 then (141, 154) else (37, 19))) else (if i.val < 832 then (if i.val < 831 then (84, 220) else (89, 99)) else (if i.val < 833 then (125, 142) else (96, 104)))) else (if i.val < 838 then (if i.val < 836 then (if i.val < 835 then (138, 14) else (141, 188)) else (if i.val < 837 then (116, 23) else (87, 176))) else (if i.val < 840 then (if i.val < 839 then (116, 41) else (28, 37)) else (if i.val < 841 then (117, 81) else (if i.val < 842 then (70, 8) else (116, 251))))))) else (if i.val < 860 then (if i.val < 851 then (if i.val < 847 then (if i.val < 845 then (if i.val < 844 then (118, 155) else (137, 146)) else (if i.val < 846 then (108, 128) else (144, 186))) else (if i.val < 849 then (if i.val < 848 then (46, 9) else (18, 150)) else (if i.val < 850 then (119, 206) else (143, 165)))) else (if i.val < 855 then (if i.val < 853 then (if i.val < 852 then (38, 224) else (1, 191)) else (if i.val < 854 then (125, 64) else (127, 222))) else (if i.val < 857 then (if i.val < 856 then (0, 69) else (114, 130)) else (if i.val < 858 then (144, 191) else (if i.val < 859 then (84, 155) else (102, 127)))))) else (if i.val < 868 then (if i.val < 864 then (if i.val < 862 then (if i.val < 861 then (112, 83) else (129, 195)) else (if i.val < 863 then (31, 54) else (79, 11))) else (if i.val < 866 then (if i.val < 865 then (76, 195) else (86, 10)) else (if i.val < 867 then (77, 89) else (141, 64)))) else (if i.val < 872 then (if i.val < 870 then (if i.val < 869 then (46, 101) else (24, 139)) else (if i.val < 871 then (116, 26) else (72, 229))) else (if i.val < 874 then (if i.val < 873 then (1, 21) else (75, 252)) else (if i.val < 875 then (53, 212) else (if i.val < 876 then (3, 39) else (133, 207)))))))) else (if i.val < 911 then (if i.val < 894 then (if i.val < 885 then (if i.val < 881 then (if i.val < 879 then (if i.val < 878 then (105, 175) else (95, 31)) else (if i.val < 880 then (139, 149) else (95, 46))) else (if i.val < 883 then (if i.val < 882 then (33, 55) else (123, 107)) else (if i.val < 884 then (0, 34) else (43, 74)))) else (if i.val < 889 then (if i.val < 887 then (if i.val < 886 then (140, 182) else (88, 97)) else (if i.val < 888 then (23, 129) else (72, 244))) else (if i.val < 891 then (if i.val < 890 then (104, 173) else (135, 232)) else (if i.val < 892 then (138, 20) else (if i.val < 893 then (102, 25) else (78, 207)))))) else (if i.val < 902 then (if i.val < 898 then (if i.val < 896 then (if i.val < 895 then (12, 54) else (127, 56)) else (if i.val < 897 then (143, 60) else (129, 29))) else (if i.val < 900 then (if i.val < 899 then (124, 22) else (135, 225)) else (if i.val < 901 then (25, 67) else (142, 179)))) else (if i.val < 906 then (if i.val < 904 then (if i.val < 903 then (122, 159) else (116, 162)) else (if i.val < 905 then (65, 217) else (70, 194))) else (if i.val < 908 then (if i.val < 907 then (8, 0) else (133, 153)) else (if i.val < 909 then (84, 123) else (if i.val < 910 then (105, 105) else (3, 111))))))) else (if i.val < 928 then (if i.val < 919 then (if i.val < 915 then (if i.val < 913 then (if i.val < 912 then (43, 9) else (72, 104)) else (if i.val < 914 then (50, 89) else (116, 177))) else (if i.val < 917 then (if i.val < 916 then (94, 83) else (122, 62)) else (if i.val < 918 then (30, 104) else (2, 16)))) else (if i.val < 923 then (if i.val < 921 then (if i.val < 920 then (87, 96) else (51, 251)) else (if i.val < 922 then (112, 1) else (131, 68))) else (if i.val < 925 then (if i.val < 924 then (35, 145) else (25, 82)) else (if i.val < 926 then (127, 208) else (if i.val < 927 then (61, 150) else (96, 139)))))) else (if i.val < 936 then (if i.val < 932 then (if i.val < 930 then (if i.val < 929 then (111, 13) else (105, 133)) else (if i.val < 931 then (104, 157) else (22, 11))) else (if i.val < 934 then (if i.val < 933 then (97, 117) else (122, 239)) else (if i.val < 935 then (85, 220) else (137, 216)))) else (if i.val < 940 then (if i.val < 938 then (if i.val < 937 then (76, 149) else (134, 38)) else (if i.val < 939 then (24, 99) else (126, 136))) else (if i.val < 942 then (if i.val < 941 then (133, 58) else (29, 63)) else (if i.val < 943 then (124, 244) else (if i.val < 944 then (140, 116) else (98, 243))))))))) else (if i.val < 1012 then (if i.val < 978 then (if i.val < 961 then (if i.val < 953 then (if i.val < 949 then (if i.val < 947 then (if i.val < 946 then (138, 220) else (62, 254)) else (if i.val < 948 then (95, 184) else (140, 208))) else (if i.val < 951 then (if i.val < 950 then (87, 154) else (28, 107)) else (if i.val < 952 then (22, 173) else (136, 180)))) else (if i.val < 957 then (if i.val < 955 then (if i.val < 954 then (114, 112) else (103, 221)) else (if i.val < 956 then (25, 103) else (60, 147))) else (if i.val < 959 then (if i.val < 958 then (133, 241) else (29, 110)) else (if i.val < 960 then (17, 197) else (110, 138))))) else (if i.val < 969 then (if i.val < 965 then (if i.val < 963 then (if i.val < 962 then (144, 63) else (60, 231)) else (if i.val < 964 then (140, 234) else (15, 66))) else (if i.val < 967 then (if i.val < 966 then (131, 144) else (133, 231)) else (if i.val < 968 then (31, 224) else (126, 163)))) else (if i.val < 973 then (if i.val < 971 then (if i.val < 970 then (68, 132) else (143, 155)) else (if i.val < 972 then (114, 40) else (26, 205))) else (if i.val < 975 then (if i.val < 974 then (84, 112) else (115, 137)) else (if i.val < 976 then (144, 189) else (if i.val < 977 then (144, 112) else (25, 162))))))) else (if i.val < 995 then (if i.val < 986 then (if i.val < 982 then (if i.val < 980 then (if i.val < 979 then (60, 225) else (107, 92)) else (if i.val < 981 then (112, 68) else (67, 129))) else (if i.val < 984 then (if i.val < 983 then (66, 8) else (143, 253)) else (if i.val < 985 then (106, 31) else (19, 132)))) else (if i.val < 990 then (if i.val < 988 then (if i.val < 987 then (16, 122) else (127, 61)) else (if i.val < 989 then (134, 180) else (10, 239))) else (if i.val < 992 then (if i.val < 991 then (130, 103) else (109, 74)) else (if i.val < 993 then (85, 195) else (if i.val < 994 then (72, 35) else (85, 31)))))) else (if i.val < 1003 then (if i.val < 999 then (if i.val < 997 then (if i.val < 996 then (62, 223) else (117, 205)) else (if i.val < 998 then (71, 98) else (0, 65))) else (if i.val < 1001 then (if i.val < 1000 then (86, 191) else (105, 226)) else (if i.val < 1002 then (140, 165) else (39, 238)))) else (if i.val < 1007 then (if i.val < 1005 then (if i.val < 1004 then (100, 34) else (106, 252)) else (if i.val < 1006 then (140, 206) else (78, 39))) else (if i.val < 1009 then (if i.val < 1008 then (65, 247) else (143, 115)) else (if i.val < 1010 then (132, 101) else (if i.val < 1011 then (91, 112) else (67, 252)))))))) else (if i.val < 1046 then (if i.val < 1029 then (if i.val < 1020 then (if i.val < 1016 then (if i.val < 1014 then (if i.val < 1013 then (119, 42) else (56, 9)) else (if i.val < 1015 then (132, 79) else (112, 11))) else (if i.val < 1018 then (if i.val < 1017 then (128, 57) else (141, 27)) else (if i.val < 1019 then (22, 234) else (73, 121)))) else (if i.val < 1024 then (if i.val < 1022 then (if i.val < 1021 then (118, 73) else (101, 108)) else (if i.val < 1023 then (142, 76) else (125, 222))) else (if i.val < 1026 then (if i.val < 1025 then (53, 123) else (123, 70)) else (if i.val < 1027 then (139, 12) else (if i.val < 1028 then (126, 164) else (93, 57)))))) else (if i.val < 1037 then (if i.val < 1033 then (if i.val < 1031 then (if i.val < 1030 then (88, 169) else (144, 3)) else (if i.val < 1032 then (139, 101) else (137, 231))) else (if i.val < 1035 then (if i.val < 1034 then (32, 116) else (79, 231)) else (if i.val < 1036 then (9, 252) else (115, 253)))) else (if i.val < 1041 then (if i.val < 1039 then (if i.val < 1038 then (139, 51) else (138, 36)) else (if i.val < 1040 then (119, 77) else (142, 87))) else (if i.val < 1043 then (if i.val < 1042 then (144, 46) else (97, 47)) else (if i.val < 1044 then (46, 105) else (if i.val < 1045 then (133, 86) else (107, 215))))))) else (if i.val < 1063 then (if i.val < 1054 then (if i.val < 1050 then (if i.val < 1048 then (if i.val < 1047 then (110, 192) else (133, 155)) else (if i.val < 1049 then (61, 170) else (136, 34))) else (if i.val < 1052 then (if i.val < 1051 then (122, 57) else (100, 43)) else (if i.val < 1053 then (138, 212) else (35, 38)))) else (if i.val < 1058 then (if i.val < 1056 then (if i.val < 1055 then (90, 81) else (131, 121)) else (if i.val < 1057 then (21, 187) else (142, 153))) else (if i.val < 1060 then (if i.val < 1059 then (104, 184) else (135, 137)) else (if i.val < 1061 then (12, 196) else (if i.val < 1062 then (33, 104) else (136, 79)))))) else (if i.val < 1071 then (if i.val < 1067 then (if i.val < 1065 then (if i.val < 1064 then (138, 37) else (91, 27)) else (if i.val < 1066 then (13, 64) else (69, 70))) else (if i.val < 1069 then (if i.val < 1068 then (142, 197) else (144, 106)) else (if i.val < 1070 then (92, 110) else (87, 145)))) else (if i.val < 1075 then (if i.val < 1073 then (if i.val < 1072 then (38, 171) else (83, 30)) else (if i.val < 1074 then (3, 30) else (0, 153))) else (if i.val < 1077 then (if i.val < 1076 then (127, 235) else (132, 93)) else (if i.val < 1078 then (104, 91) else (if i.val < 1079 then (131, 146) else (81, 63)))))))))))) else (if i.val < 1620 then (if i.val < 1350 then (if i.val < 1215 then (if i.val < 1147 then (if i.val < 1113 then (if i.val < 1096 then (if i.val < 1088 then (if i.val < 1084 then (if i.val < 1082 then (if i.val < 1081 then (100, 0) else (3, 121)) else (if i.val < 1083 then (115, 234) else (53, 134))) else (if i.val < 1086 then (if i.val < 1085 then (132, 125) else (116, 99)) else (if i.val < 1087 then (139, 163) else (83, 88)))) else (if i.val < 1092 then (if i.val < 1090 then (if i.val < 1089 then (38, 79) else (94, 162)) else (if i.val < 1091 then (124, 20) else (47, 64))) else (if i.val < 1094 then (if i.val < 1093 then (140, 78) else (47, 201)) else (if i.val < 1095 then (133, 176) else (103, 226))))) else (if i.val < 1104 then (if i.val < 1100 then (if i.val < 1098 then (if i.val < 1097 then (119, 11) else (139, 88)) else (if i.val < 1099 then (119, 185) else (41, 229))) else (if i.val < 1102 then (if i.val < 1101 then (123, 65) else (131, 201)) else (if i.val < 1103 then (125, 57) else (140, 180)))) else (if i.val < 1108 then (if i.val < 1106 then (if i.val < 1105 then (52, 55) else (52, 189)) else (if i.val < 1107 then (56, 206) else (78, 53))) else (if i.val < 1110 then (if i.val < 1109 then (122, 92) else (125, 233)) else (if i.val < 1111 then (114, 243) else (if i.val < 1112 then (30, 19) else (105, 180))))))) else (if i.val < 1130 then (if i.val < 1121 then (if i.val < 1117 then (if i.val < 1115 then (if i.val < 1114 then (129, 107) else (139, 174)) else (if i.val < 1116 then (15, 5) else (144, 8))) else (if i.val < 1119 then (if i.val < 1118 then (124, 242) else (133, 76)) else (if i.val < 1120 then (10, 222) else (133, 37)))) else (if i.val < 1125 then (if i.val < 1123 then (if i.val < 1122 then (120, 182) else (41, 32)) else (if i.val < 1124 then (97, 42) else (50, 5))) else (if i.val < 1127 then (if i.val < 1126 then (16, 44) else (107, 140)) else (if i.val < 1128 then (0, 4) else (if i.val < 1129 then (127, 149) else (112, 149)))))) else (if i.val < 1138 then (if i.val < 1134 then (if i.val < 1132 then (if i.val < 1131 then (77, 169) else (135, 191)) else (if i.val < 1133 then (136, 39) else (102, 36))) else (if i.val < 1136 then (if i.val < 1135 then (131, 124) else (135, 238)) else (if i.val < 1137 then (130, 71) else (111, 114)))) else (if i.val < 1142 then (if i.val < 1140 then (if i.val < 1139 then (31, 245) else (50, 91)) else (if i.val < 1141 then (83, 77) else (24, 28))) else (if i.val < 1144 then (if i.val < 1143 then (122, 154) else (144, 56)) else (if i.val < 1145 then (121, 29) else (if i.val < 1146 then (80, 27) else (143, 58)))))))) else (if i.val < 1181 then (if i.val < 1164 then (if i.val < 1155 then (if i.val < 1151 then (if i.val < 1149 then (if i.val < 1148 then (47, 229) else (75, 185)) else (if i.val < 1150 then (85, 208) else (22, 105))) else (if i.val < 1153 then (if i.val < 1152 then (60, 232) else (132, 41)) else (if i.val < 1154 then (72, 26) else (114, 61)))) else (if i.val < 1159 then (if i.val < 1157 then (if i.val < 1156 then (102, 163) else (74, 143)) else (if i.val < 1158 then (90, 178) else (129, 216))) else (if i.val < 1161 then (if i.val < 1160 then (138, 30) else (78, 187)) else (if i.val < 1162 then (91, 62) else (if i.val < 1163 then (142, 161) else (81, 143)))))) else (if i.val < 1172 then (if i.val < 1168 then (if i.val < 1166 then (if i.val < 1165 then (33, 125) else (87, 112)) else (if i.val < 1167 then (60, 242) else (69, 28))) else (if i.val < 1170 then (if i.val < 1169 then (94, 93) else (132, 213)) else (if i.val < 1171 then (113, 186) else (76, 152)))) else (if i.val < 1176 then (if i.val < 1174 then (if i.val < 1173 then (51, 152) else (141, 139)) else (if i.val < 1175 then (11, 29) else (133, 199))) else (if i.val < 1178 then (if i.val < 1177 then (128, 254) else (112, 215)) else (if i.val < 1179 then (100, 16) else (if i.val < 1180 then (106, 101) else (90, 179))))))) else (if i.val < 1198 then (if i.val < 1189 then (if i.val < 1185 then (if i.val < 1183 then (if i.val < 1182 then (128, 160) else (140, 109)) else (if i.val < 1184 then (137, 140) else (131, 194))) else (if i.val < 1187 then (if i.val < 1186 then (120, 27) else (135, 41)) else (if i.val < 1188 then (85, 130) else (80, 72)))) else (if i.val < 1193 then (if i.val < 1191 then (if i.val < 1190 then (51, 53) else (4, 94)) else (if i.val < 1192 then (9, 135) else (130, 28))) else (if i.val < 1195 then (if i.val < 1194 then (31, 217) else (137, 186)) else (if i.val < 1196 then (51, 88) else (if i.val < 1197 then (135, 72) else (119, 191)))))) else (if i.val < 1206 then (if i.val < 1202 then (if i.val < 1200 then (if i.val < 1199 then (138, 44) else (57, 153)) else (if i.val < 1201 then (84, 154) else (112, 34))) else (if i.val < 1204 then (if i.val < 1203 then (136, 35) else (68, 9)) else (if i.val < 1205 then (143, 18) else (97, 50)))) else (if i.val < 1210 then (if i.val < 1208 then (if i.val < 1207 then (104, 174) else (139, 239)) else (if i.val < 1209 then (135, 220) else (142, 148))) else (if i.val < 1212 then (if i.val < 1211 then (117, 243) else (72, 202)) else (if i.val < 1213 then (144, 61) else (if i.val < 1214 then (19, 212) else (22, 154))))))))) else (if i.val < 1282 then (if i.val < 1248 then (if i.val < 1231 then (if i.val < 1223 then (if i.val < 1219 then (if i.val < 1217 then (if i.val < 1216 then (53, 137) else (122, 104)) else (if i.val < 1218 then (133, 171) else (41, 27))) else (if i.val < 1221 then (if i.val < 1220 then (141, 48) else (122, 170)) else (if i.val < 1222 then (122, 190) else (19, 254)))) else (if i.val < 1227 then (if i.val < 1225 then (if i.val < 1224 then (106, 14) else (135, 38)) else (if i.val < 1226 then (129, 199) else (143, 154))) else (if i.val < 1229 then (if i.val < 1228 then (77, 158) else (140, 245)) else (if i.val < 1230 then (138, 5) else (121, 46))))) else (if i.val < 1239 then (if i.val < 1235 then (if i.val < 1233 then (if i.val < 1232 then (113, 76) else (126, 197)) else (if i.val < 1234 then (42, 160) else (143, 97))) else (if i.val < 1237 then (if i.val < 1236 then (132, 189) else (93, 238)) else (if i.val < 1238 then (137, 89) else (130, 170)))) else (if i.val < 1243 then (if i.val < 1241 then (if i.val < 1240 then (107, 138) else (113, 63)) else (if i.val < 1242 then (4, 104) else (137, 86))) else (if i.val < 1245 then (if i.val < 1244 then (142, 170) else (116, 236)) else (if i.val < 1246 then (65, 201) else (if i.val < 1247 then (125, 68) else (85, 54))))))) else (if i.val < 1265 then (if i.val < 1256 then (if i.val < 1252 then (if i.val < 1250 then (if i.val < 1249 then (112, 71) else (108, 46)) else (if i.val < 1251 then (126, 104) else (131, 25))) else (if i.val < 1254 then (if i.val < 1253 then (115, 190) else (134, 189)) else (if i.val < 1255 then (129, 33) else (99, 132)))) else (if i.val < 1260 then (if i.val < 1258 then (if i.val < 1257 then (136, 126) else (87, 122)) else (if i.val < 1259 then (144, 81) else (139, 152))) else (if i.val < 1262 then (if i.val < 1261 then (107, 245) else (116, 230)) else (if i.val < 1263 then (109, 51) else (if i.val < 1264 then (132, 38) else (87, 132)))))) else (if i.val < 1273 then (if i.val < 1269 then (if i.val < 1267 then (if i.val < 1266 then (133, 219) else (23, 36)) else (if i.val < 1268 then (55, 241) else (127, 33))) else (if i.val < 1271 then (if i.val < 1270 then (64, 50) else (134, 204)) else (if i.val < 1272 then (99, 89) else (141, 69)))) else (if i.val < 1277 then (if i.val < 1275 then (if i.val < 1274 then (101, 128) else (102, 110)) else (if i.val < 1276 then (123, 140) else (58, 121))) else (if i.val < 1279 then (if i.val < 1278 then (20, 202) else (140, 143)) else (if i.val < 1280 then (142, 24) else (if i.val < 1281 then (125, 244) else (64, 13)))))))) else (if i.val < 1316 then (if i.val < 1299 then (if i.val < 1290 then (if i.val < 1286 then (if i.val < 1284 then (if i.val < 1283 then (131, 58) else (112, 227)) else (if i.val < 1285 then (59, 238) else (142, 145))) else (if i.val < 1288 then (if i.val < 1287 then (108, 137) else (144, 178)) else (if i.val < 1289 then (56, 218) else (106, 248)))) else (if i.val < 1294 then (if i.val < 1292 then (if i.val < 1291 then (33, 50) else (83, 182)) else (if i.val < 1293 then (38, 232) else (55, 107))) else (if i.val < 1296 then (if i.val < 1295 then (80, 97) else (109, 224)) else (if i.val < 1297 then (86, 8) else (if i.val < 1298 then (124, 73) else (66, 244)))))) else (if i.val < 1307 then (if i.val < 1303 then (if i.val < 1301 then (if i.val < 1300 then (141, 109) else (143, 250)) else (if i.val < 1302 then (61, 89) else (136, 195))) else (if i.val < 1305 then (if i.val < 1304 then (134, 93) else (137, 101)) else (if i.val < 1306 then (77, 130) else (106, 152)))) else (if i.val < 1311 then (if i.val < 1309 then (if i.val < 1308 then (119, 69) else (83, 149)) else (if i.val < 1310 then (139, 6) else (33, 189))) else (if i.val < 1313 then (if i.val < 1312 then (36, 118) else (119, 239)) else (if i.val < 1314 then (144, 9) else (if i.val < 1315 then (134, 225) else (101, 1))))))) else (if i.val < 1333 then (if i.val < 1324 then (if i.val < 1320 then (if i.val < 1318 then (if i.val < 1317 then (110, 103) else (138, 197)) else (if i.val < 1319 then (22, 126) else (117, 195))) else (if i.val < 1322 then (if i.val < 1321 then (87, 162) else (84, 156)) else (if i.val < 1323 then (116, 78) else (137, 116)))) else (if i.val < 1328 then (if i.val < 1326 then (if i.val < 1325 then (71, 75) else (28, 119)) else (if i.val < 1327 then (129, 4) else (95, 53))) else (if i.val < 1330 then (if i.val < 1329 then (110, 44) else (65, 133)) else (if i.val < 1331 then (114, 146) else (if i.val < 1332 then (133, 119) else (143, 134)))))) else (if i.val < 1341 then (if i.val < 1337 then (if i.val < 1335 then (if i.val < 1334 then (124, 213) else (105, 108)) else (if i.val < 1336 then (135, 215) else (137, 143))) else (if i.val < 1339 then (if i.val < 1338 then (74, 61) else (139, 2)) else (if i.val < 1340 then (28, 26) else (118, 82)))) else (if i.val < 1345 then (if i.val < 1343 then (if i.val < 1342 then (14, 139) else (48, 168)) else (if i.val < 1344 then (141, 70) else (59, 250))) else (if i.val < 1347 then (if i.val < 1346 then (42, 50) else (45, 122)) else (if i.val < 1348 then (122, 9) else (if i.val < 1349 then (144, 226) else (55, 234)))))))))) else (if i.val < 1485 then (if i.val < 1417 then (if i.val < 1383 then (if i.val < 1366 then (if i.val < 1358 then (if i.val < 1354 then (if i.val < 1352 then (if i.val < 1351 then (88, 226) else (124, 151)) else (if i.val < 1353 then (78, 170) else (89, 194))) else (if i.val < 1356 then (if i.val < 1355 then (143, 63) else (139, 227)) else (if i.val < 1357 then (99, 155) else (106, 94)))) else (if i.val < 1362 then (if i.val < 1360 then (if i.val < 1359 then (133, 162) else (108, 172)) else (if i.val < 1361 then (83, 188) else (111, 157))) else (if i.val < 1364 then (if i.val < 1363 then (50, 203) else (129, 127)) else (if i.val < 1365 then (9, 144) else (66, 254))))) else (if i.val < 1374 then (if i.val < 1370 then (if i.val < 1368 then (if i.val < 1367 then (110, 189) else (76, 168)) else (if i.val < 1369 then (139, 225) else (136, 57))) else (if i.val < 1372 then (if i.val < 1371 then (59, 59) else (126, 199)) else (if i.val < 1373 then (37, 158) else (117, 164)))) else (if i.val < 1378 then (if i.val < 1376 then (if i.val < 1375 then (144, 19) else (126, 177)) else (if i.val < 1377 then (40, 94) else (11, 50))) else (if i.val < 1380 then (if i.val < 1379 then (138, 85) else (119, 105)) else (if i.val < 1381 then (110, 212) else (if i.val < 1382 then (61, 46) else (99, 35))))))) else (if i.val < 1400 then (if i.val < 1391 then (if i.val < 1387 then (if i.val < 1385 then (if i.val < 1384 then (85, 28) else (86, 59)) else (if i.val < 1386 then (85, 127) else (140, 248))) else (if i.val < 1389 then (if i.val < 1388 then (98, 184) else (134, 106)) else (if i.val < 1390 then (111, 45) else (131, 232)))) else (if i.val < 1395 then (if i.val < 1393 then (if i.val < 1392 then (143, 35) else (130, 251)) else (if i.val < 1394 then (122, 194) else (139, 86))) else (if i.val < 1397 then (if i.val < 1396 then (137, 78) else (115, 221)) else (if i.val < 1398 then (63, 12) else (if i.val < 1399 then (135, 186) else (34, 166)))))) else (if i.val < 1408 then (if i.val < 1404 then (if i.val < 1402 then (if i.val < 1401 then (127, 90) else (5, 7)) else (if i.val < 1403 then (23, 91) else (83, 150))) else (if i.val < 1406 then (if i.val < 1405 then (128, 233) else (83, 169)) else (if i.val < 1407 then (137, 129) else (112, 50)))) else (if i.val < 1412 then (if i.val < 1410 then (if i.val < 1409 then (108, 181) else (43, 223)) else (if i.val < 1411 then (78, 100) else (141, 193))) else (if i.val < 1414 then (if i.val < 1413 then (96, 12) else (141, 132)) else (if i.val < 1415 then (51, 254) else (if i.val < 1416 then (116, 6) else (67, 134)))))))) else (if i.val < 1451 then (if i.val < 1434 then (if i.val < 1425 then (if i.val < 1421 then (if i.val < 1419 then (if i.val < 1418 then (123, 219) else (124, 222)) else (if i.val < 1420 then (101, 195) else (36, 22))) else (if i.val < 1423 then (if i.val < 1422 then (87, 239) else (106, 48)) else (if i.val < 1424 then (138, 255) else (118, 61)))) else (if i.val < 1429 then (if i.val < 1427 then (if i.val < 1426 then (20, 32) else (13, 208)) else (if i.val < 1428 then (143, 167) else (90, 227))) else (if i.val < 1431 then (if i.val < 1430 then (27, 221) else (96, 83)) else (if i.val < 1432 then (83, 107) else (if i.val < 1433 then (25, 27) else (88, 243)))))) else (if i.val < 1442 then (if i.val < 1438 then (if i.val < 1436 then (if i.val < 1435 then (117, 252) else (84, 59)) else (if i.val < 1437 then (121, 24) else (143, 193))) else (if i.val < 1440 then (if i.val < 1439 then (125, 3) else (128, 134)) else (if i.val < 1441 then (46, 144) else (131, 16)))) else (if i.val < 1446 then (if i.val < 1444 then (if i.val < 1443 then (104, 66) else (118, 111)) else (if i.val < 1445 then (98, 19) else (106, 225))) else (if i.val < 1448 then (if i.val < 1447 then (50, 97) else (68, 222)) else (if i.val < 1449 then (125, 115) else (if i.val < 1450 then (33, 135) else (132, 246))))))) else (if i.val < 1468 then (if i.val < 1459 then (if i.val < 1455 then (if i.val < 1453 then (if i.val < 1452 then (100, 147) else (141, 195)) else (if i.val < 1454 then (112, 200) else (124, 142))) else (if i.val < 1457 then (if i.val < 1456 then (90, 223) else (141, 80)) else (if i.val < 1458 then (124, 203) else (135, 28)))) else (if i.val < 1463 then (if i.val < 1461 then (if i.val < 1460 then (107, 202) else (59, 22)) else (if i.val < 1462 then (103, 214) else (56, 42))) else (if i.val < 1465 then (if i.val < 1464 then (117, 22) else (80, 6)) else (if i.val < 1466 then (57, 165) else (if i.val < 1467 then (92, 58) else (141, 155)))))) else (if i.val < 1476 then (if i.val < 1472 then (if i.val < 1470 then (if i.val < 1469 then (66, 209) else (127, 50)) else (if i.val < 1471 then (137, 165) else (140, 9))) else (if i.val < 1474 then (if i.val < 1473 then (142, 146) else (120, 166)) else (if i.val < 1475 then (83, 192) else (104, 144)))) else (if i.val < 1480 then (if i.val < 1478 then (if i.val < 1477 then (10, 130) else (133, 123)) else (if i.val < 1479 then (117, 208) else (143, 66))) else (if i.val < 1482 then (if i.val < 1481 then (100, 46) else (56, 86)) else (if i.val < 1483 then (86, 232) else (if i.val < 1484 then (138, 221) else (68, 68))))))))) else (if i.val < 1552 then (if i.val < 1518 then (if i.val < 1501 then (if i.val < 1493 then (if i.val < 1489 then (if i.val < 1487 then (if i.val < 1486 then (25, 14) else (28, 213)) else (if i.val < 1488 then (112, 183) else (141, 14))) else (if i.val < 1491 then (if i.val < 1490 then (141, 158) else (52, 96)) else (if i.val < 1492 then (44, 190) else (104, 15)))) else (if i.val < 1497 then (if i.val < 1495 then (if i.val < 1494 then (95, 203) else (42, 179)) else (if i.val < 1496 then (70, 225) else (65, 7))) else (if i.val < 1499 then (if i.val < 1498 then (56, 197) else (143, 235)) else (if i.val < 1500 then (49, 34) else (142, 16))))) else (if i.val < 1509 then (if i.val < 1505 then (if i.val < 1503 then (if i.val < 1502 then (18, 88) else (126, 238)) else (if i.val < 1504 then (18, 98) else (142, 228))) else (if i.val < 1507 then (if i.val < 1506 then (138, 99) else (139, 136)) else (if i.val < 1508 then (60, 152) else (133, 252)))) else (if i.val < 1513 then (if i.val < 1511 then (if i.val < 1510 then (109, 125) else (139, 128)) else (if i.val < 1512 then (127, 236) else (45, 223))) else (if i.val < 1515 then (if i.val < 1514 then (10, 212) else (83, 246)) else (if i.val < 1516 then (78, 162) else (if i.val < 1517 then (34, 209) else (132, 222))))))) else (if i.val < 1535 then (if i.val < 1526 then (if i.val < 1522 then (if i.val < 1520 then (if i.val < 1519 then (125, 231) else (30, 207)) else (if i.val < 1521 then (91, 175) else (116, 205))) else (if i.val < 1524 then (if i.val < 1523 then (136, 103) else (137, 234)) else (if i.val < 1525 then (84, 82) else (125, 76)))) else (if i.val < 1530 then (if i.val < 1528 then (if i.val < 1527 then (138, 186) else (32, 66)) else (if i.val < 1529 then (103, 177) else (119, 85))) else (if i.val < 1532 then (if i.val < 1531 then (131, 154) else (37, 219)) else (if i.val < 1533 then (144, 179) else (if i.val < 1534 then (36, 245) else (135, 135)))))) else (if i.val < 1543 then (if i.val < 1539 then (if i.val < 1537 then (if i.val < 1536 then (108, 39) else (138, 146)) else (if i.val < 1538 then (76, 37) else (104, 215))) else (if i.val < 1541 then (if i.val < 1540 then (144, 143) else (84, 238)) else (if i.val < 1542 then (120, 55) else (86, 167)))) else (if i.val < 1547 then (if i.val < 1545 then (if i.val < 1544 then (85, 121) else (127, 200)) else (if i.val < 1546 then (129, 91) else (18, 30))) else (if i.val < 1549 then (if i.val < 1548 then (127, 86) else (122, 31)) else (if i.val < 1550 then (138, 240) else (if i.val < 1551 then (134, 50) else (143, 64)))))))) else (if i.val < 1586 then (if i.val < 1569 then (if i.val < 1560 then (if i.val < 1556 then (if i.val < 1554 then (if i.val < 1553 then (110, 232) else (142, 175)) else (if i.val < 1555 then (90, 67) else (140, 186))) else (if i.val < 1558 then (if i.val < 1557 then (87, 68) else (19, 194)) else (if i.val < 1559 then (56, 78) else (95, 136)))) else (if i.val < 1564 then (if i.val < 1562 then (if i.val < 1561 then (106, 53) else (143, 68)) else (if i.val < 1563 then (122, 238) else (126, 119))) else (if i.val < 1566 then (if i.val < 1565 then (140, 60) else (132, 74)) else (if i.val < 1567 then (78, 230) else (if i.val < 1568 then (132, 58) else (24, 154)))))) else (if i.val < 1577 then (if i.val < 1573 then (if i.val < 1571 then (if i.val < 1570 then (115, 239) else (121, 95)) else (if i.val < 1572 then (126, 128) else (51, 239))) else (if i.val < 1575 then (if i.val < 1574 then (118, 37) else (3, 140)) else (if i.val < 1576 then (108, 10) else (142, 158)))) else (if i.val < 1581 then (if i.val < 1579 then (if i.val < 1578 then (40, 20) else (134, 52)) else (if i.val < 1580 then (68, 129) else (140, 23))) else (if i.val < 1583 then (if i.val < 1582 then (96, 170) else (144, 185)) else (if i.val < 1584 then (65, 172) else (if i.val < 1585 then (53, 128) else (124, 206))))))) else (if i.val < 1603 then (if i.val < 1594 then (if i.val < 1590 then (if i.val < 1588 then (if i.val < 1587 then (141, 229) else (92, 28)) else (if i.val < 1589 then (48, 150) else (135, 35))) else (if i.val < 1592 then (if i.val < 1591 then (118, 251) else (26, 94)) else (if i.val < 1593 then (129, 80) else (100, 144)))) else (if i.val < 1598 then (if i.val < 1596 then (if i.val < 1595 then (69, 116) else (89, 40)) else (if i.val < 1597 then (94, 204) else (138, 148))) else (if i.val < 1600 then (if i.val < 1599 then (111, 20) else (20, 98)) else (if i.val < 1601 then (43, 243) else (if i.val < 1602 then (76, 19) else (107, 219)))))) else (if i.val < 1611 then (if i.val < 1607 then (if i.val < 1605 then (if i.val < 1604 then (137, 56) else (116, 115)) else (if i.val < 1606 then (63, 124) else (107, 235))) else (if i.val < 1609 then (if i.val < 1608 then (126, 97) else (123, 149)) else (if i.val < 1610 then (136, 192) else (85, 17)))) else (if i.val < 1615 then (if i.val < 1613 then (if i.val < 1612 then (71, 224) else (36, 253)) else (if i.val < 1614 then (120, 36) else (132, 212))) else (if i.val < 1617 then (if i.val < 1616 then (142, 120) else (79, 47)) else (if i.val < 1618 then (140, 24) else (if i.val < 1619 then (129, 218) else (140, 112))))))))))) else (if i.val < 1890 then (if i.val < 1755 then (if i.val < 1687 then (if i.val < 1653 then (if i.val < 1636 then (if i.val < 1628 then (if i.val < 1624 then (if i.val < 1622 then (if i.val < 1621 then (25, 17) else (49, 252)) else (if i.val < 1623 then (117, 66) else (136, 118))) else (if i.val < 1626 then (if i.val < 1625 then (141, 96) else (142, 164)) else (if i.val < 1627 then (113, 192) else (23, 205)))) else (if i.val < 1632 then (if i.val < 1630 then (if i.val < 1629 then (136, 31) else (117, 20)) else (if i.val < 1631 then (137, 38) else (77, 196))) else (if i.val < 1634 then (if i.val < 1633 then (131, 226) else (118, 168)) else (if i.val < 1635 then (141, 120) else (77, 239))))) else (if i.val < 1644 then (if i.val < 1640 then (if i.val < 1638 then (if i.val < 1637 then (93, 249) else (120, 2)) else (if i.val < 1639 then (144, 209) else (139, 185))) else (if i.val < 1642 then (if i.val < 1641 then (105, 114) else (135, 179)) else (if i.val < 1643 then (37, 227) else (130, 87)))) else (if i.val < 1648 then (if i.val < 1646 then (if i.val < 1645 then (134, 139) else (34, 7)) else (if i.val < 1647 then (12, 236) else (0, 199))) else (if i.val < 1650 then (if i.val < 1649 then (65, 13) else (75, 131)) else (if i.val < 1651 then (119, 148) else (if i.val < 1652 then (35, 99) else (103, 9))))))) else (if i.val < 1670 then (if i.val < 1661 then (if i.val < 1657 then (if i.val < 1655 then (if i.val < 1654 then (94, 108) else (138, 52)) else (if i.val < 1656 then (6, 137) else (126, 239))) else (if i.val < 1659 then (if i.val < 1658 then (143, 59) else (121, 76)) else (if i.val < 1660 then (126, 150) else (91, 128)))) else (if i.val < 1665 then (if i.val < 1663 then (if i.val < 1662 then (94, 111) else (108, 116)) else (if i.val < 1664 then (142, 213) else (81, 45))) else (if i.val < 1667 then (if i.val < 1666 then (137, 188) else (111, 35)) else (if i.val < 1668 then (56, 26) else (if i.val < 1669 then (134, 175) else (142, 244)))))) else (if i.val < 1678 then (if i.val < 1674 then (if i.val < 1672 then (if i.val < 1671 then (26, 53) else (20, 51)) else (if i.val < 1673 then (95, 86) else (70, 12))) else (if i.val < 1676 then (if i.val < 1675 then (138, 109) else (72, 155)) else (if i.val < 1677 then (106, 236) else (41, 245)))) else (if i.val < 1682 then (if i.val < 1680 then (if i.val < 1679 then (94, 26) else (98, 201)) else (if i.val < 1681 then (114, 18) else (120, 11))) else (if i.val < 1684 then (if i.val < 1683 then (72, 45) else (73, 33)) else (if i.val < 1685 then (51, 184) else (if i.val < 1686 then (58, 104) else (142, 130)))))))) else (if i.val < 1721 then (if i.val < 1704 then (if i.val < 1695 then (if i.val < 1691 then (if i.val < 1689 then (if i.val < 1688 then (123, 128) else (78, 183)) else (if i.val < 1690 then (130, 38) else (123, 74))) else (if i.val < 1693 then (if i.val < 1692 then (45, 184) else (139, 180)) else (if i.val < 1694 then (126, 113) else (86, 22)))) else (if i.val < 1699 then (if i.val < 1697 then (if i.val < 1696 then (56, 246) else (140, 113)) else (if i.val < 1698 then (137, 174) else (123, 164))) else (if i.val < 1701 then (if i.val < 1700 then (125, 223) else (70, 211)) else (if i.val < 1702 then (133, 147) else (if i.val < 1703 then (140, 88) else (64, 89)))))) else (if i.val < 1712 then (if i.val < 1708 then (if i.val < 1706 then (if i.val < 1705 then (128, 40) else (133, 117)) else (if i.val < 1707 then (141, 24) else (116, 203))) else (if i.val < 1710 then (if i.val < 1709 then (95, 114) else (40, 203)) else (if i.val < 1711 then (136, 156) else (139, 208)))) else (if i.val < 1716 then (if i.val < 1714 then (if i.val < 1713 then (38, 155) else (140, 158)) else (if i.val < 1715 then (116, 225) else (66, 173))) else (if i.val < 1718 then (if i.val < 1717 then (130, 139) else (75, 140)) else (if i.val < 1719 then (61, 24) else (if i.val < 1720 then (106, 229) else (85, 217))))))) else (if i.val < 1738 then (if i.val < 1729 then (if i.val < 1725 then (if i.val < 1723 then (if i.val < 1722 then (121, 97) else (144, 165)) else (if i.val < 1724 then (136, 18) else (138, 86))) else (if i.val < 1727 then (if i.val < 1726 then (76, 228) else (37, 200)) else (if i.val < 1728 then (129, 214) else (40, 164)))) else (if i.val < 1733 then (if i.val < 1731 then (if i.val < 1730 then (24, 239) else (78, 184)) else (if i.val < 1732 then (72, 183) else (63, 188))) else (if i.val < 1735 then (if i.val < 1734 then (127, 224) else (57, 178)) else (if i.val < 1736 then (44, 154) else (if i.val < 1737 then (60, 56) else (109, 249)))))) else (if i.val < 1746 then (if i.val < 1742 then (if i.val < 1740 then (if i.val < 1739 then (136, 47) else (108, 195)) else (if i.val < 1741 then (58, 237) else (112, 205))) else (if i.val < 1744 then (if i.val < 1743 then (141, 233) else (129, 31)) else (if i.val < 1745 then (143, 1) else (141, 185)))) else (if i.val < 1750 then (if i.val < 1748 then (if i.val < 1747 then (61, 5) else (135, 168)) else (if i.val < 1749 then (92, 19) else (97, 146))) else (if i.val < 1752 then (if i.val < 1751 then (109, 207) else (137, 178)) else (if i.val < 1753 then (91, 111) else (if i.val < 1754 then (125, 74) else (130, 78))))))))) else (if i.val < 1822 then (if i.val < 1788 then (if i.val < 1771 then (if i.val < 1763 then (if i.val < 1759 then (if i.val < 1757 then (if i.val < 1756 then (119, 58) else (118, 112)) else (if i.val < 1758 then (137, 42) else (84, 235))) else (if i.val < 1761 then (if i.val < 1760 then (95, 163) else (120, 138)) else (if i.val < 1762 then (6, 221) else (8, 40)))) else (if i.val < 1767 then (if i.val < 1765 then (if i.val < 1764 then (126, 215) else (120, 116)) else (if i.val < 1766 then (114, 59) else (59, 154))) else (if i.val < 1769 then (if i.val < 1768 then (5, 26) else (34, 119)) else (if i.val < 1770 then (140, 26) else (68, 113))))) else (if i.val < 1779 then (if i.val < 1775 then (if i.val < 1773 then (if i.val < 1772 then (123, 26) else (125, 28)) else (if i.val < 1774 then (116, 239) else (93, 67))) else (if i.val < 1777 then (if i.val < 1776 then (127, 155) else (135, 145)) else (if i.val < 1778 then (136, 251) else (111, 24)))) else (if i.val < 1783 then (if i.val < 1781 then (if i.val < 1780 then (129, 239) else (8, 207)) else (if i.val < 1782 then (119, 249) else (141, 101))) else (if i.val < 1785 then (if i.val < 1784 then (144, 29) else (91, 80)) else (if i.val < 1786 then (131, 252) else (if i.val < 1787 then (22, 2) else (131, 255))))))) else (if i.val < 1805 then (if i.val < 1796 then (if i.val < 1792 then (if i.val < 1790 then (if i.val < 1789 then (136, 190) else (116, 63)) else (if i.val < 1791 then (82, 88) else (95, 234))) else (if i.val < 1794 then (if i.val < 1793 then (59, 180) else (102, 180)) else (if i.val < 1795 then (142, 40) else (116, 1)))) else (if i.val < 1800 then (if i.val < 1798 then (if i.val < 1797 then (138, 198) else (23, 155)) else (if i.val < 1799 then (141, 133) else (128, 145))) else (if i.val < 1802 then (if i.val < 1801 then (18, 212) else (94, 190)) else (if i.val < 1803 then (136, 19) else (if i.val < 1804 then (143, 195) else (41, 202)))))) else (if i.val < 1813 then (if i.val < 1809 then (if i.val < 1807 then (if i.val < 1806 then (128, 184) else (120, 250)) else (if i.val < 1808 then (139, 210) else (144, 65))) else (if i.val < 1811 then (if i.val < 1810 then (142, 4) else (105, 63)) else (if i.val < 1812 then (128, 224) else (136, 42)))) else (if i.val < 1817 then (if i.val < 1815 then (if i.val < 1814 then (33, 40) else (111, 120)) else (if i.val < 1816 then (120, 195) else (32, 30))) else (if i.val < 1819 then (if i.val < 1818 then (119, 152) else (138, 25)) else (if i.val < 1820 then (61, 62) else (if i.val < 1821 then (139, 206) else (23, 102)))))))) else (if i.val < 1856 then (if i.val < 1839 then (if i.val < 1830 then (if i.val < 1826 then (if i.val < 1824 then (if i.val < 1823 then (115, 139) else (135, 115)) else (if i.val < 1825 then (143, 106) else (137, 218))) else (if i.val < 1828 then (if i.val < 1827 then (37, 184) else (135, 74)) else (if i.val < 1829 then (113, 209) else (134, 7)))) else (if i.val < 1834 then (if i.val < 1832 then (if i.val < 1831 then (140, 181) else (120, 123)) else (if i.val < 1833 then (45, 207) else (124, 230))) else (if i.val < 1836 then (if i.val < 1835 then (107, 124) else (41, 212)) else (if i.val < 1837 then (65, 163) else (if i.val < 1838 then (98, 120) else (144, 130)))))) else (if i.val < 1847 then (if i.val < 1843 then (if i.val < 1841 then (if i.val < 1840 then (100, 47) else (140, 219)) else (if i.val < 1842 then (18, 97) else (137, 67))) else (if i.val < 1845 then (if i.val < 1844 then (102, 254) else (96, 62)) else (if i.val < 1846 then (142, 59) else (43, 238)))) else (if i.val < 1851 then (if i.val < 1849 then (if i.val < 1848 then (52, 149) else (133, 90)) else (if i.val < 1850 then (128, 173) else (136, 110))) else (if i.val < 1853 then (if i.val < 1852 then (71, 185) else (49, 222)) else (if i.val < 1854 then (74, 164) else (if i.val < 1855 then (81, 128) else (143, 220))))))) else (if i.val < 1873 then (if i.val < 1864 then (if i.val < 1860 then (if i.val < 1858 then (if i.val < 1857 then (16, 217) else (20, 205)) else (if i.val < 1859 then (128, 247) else (47, 168))) else (if i.val < 1862 then (if i.val < 1861 then (129, 32) else (122, 127)) else (if i.val < 1863 then (98, 82) else (139, 34)))) else (if i.val < 1868 then (if i.val < 1866 then (if i.val < 1865 then (52, 237) else (102, 104)) else (if i.val < 1867 then (139, 66) else (75, 135))) else (if i.val < 1870 then (if i.val < 1869 then (36, 115) else (82, 68)) else (if i.val < 1871 then (88, 12) else (if i.val < 1872 then (141, 200) else (53, 14)))))) else (if i.val < 1881 then (if i.val < 1877 then (if i.val < 1875 then (if i.val < 1874 then (131, 30) else (89, 109)) else (if i.val < 1876 then (112, 79) else (119, 54))) else (if i.val < 1879 then (if i.val < 1878 then (104, 63) else (141, 84)) else (if i.val < 1880 then (140, 131) else (132, 87)))) else (if i.val < 1885 then (if i.val < 1883 then (if i.val < 1882 then (105, 222) else (136, 185)) else (if i.val < 1884 then (18, 240) else (58, 36))) else (if i.val < 1887 then (if i.val < 1886 then (115, 240) else (133, 118)) else (if i.val < 1888 then (130, 83) else (if i.val < 1889 then (130, 91) else (46, 158)))))))))) else (if i.val < 2025 then (if i.val < 1957 then (if i.val < 1923 then (if i.val < 1906 then (if i.val < 1898 then (if i.val < 1894 then (if i.val < 1892 then (if i.val < 1891 then (116, 24) else (115, 247)) else (if i.val < 1893 then (135, 210) else (109, 223))) else (if i.val < 1896 then (if i.val < 1895 then (131, 236) else (118, 107)) else (if i.val < 1897 then (141, 156) else (122, 23)))) else (if i.val < 1902 then (if i.val < 1900 then (if i.val < 1899 then (141, 52) else (21, 33)) else (if i.val < 1901 then (144, 16) else (68, 146))) else (if i.val < 1904 then (if i.val < 1903 then (6, 6) else (122, 60)) else (if i.val < 1905 then (107, 27) else (85, 40))))) else (if i.val < 1914 then (if i.val < 1910 then (if i.val < 1908 then (if i.val < 1907 then (56, 254) else (134, 240)) else (if i.val < 1909 then (42, 57) else (84, 252))) else (if i.val < 1912 then (if i.val < 1911 then (137, 198) else (144, 74)) else (if i.val < 1913 then (86, 237) else (135, 20)))) else (if i.val < 1918 then (if i.val < 1916 then (if i.val < 1915 then (138, 22) else (94, 246)) else (if i.val < 1917 then (28, 79) else (139, 20))) else (if i.val < 1920 then (if i.val < 1919 then (110, 2) else (133, 69)) else (if i.val < 1921 then (143, 15) else (if i.val < 1922 then (136, 46) else (114, 104))))))) else (if i.val < 1940 then (if i.val < 1931 then (if i.val < 1927 then (if i.val < 1925 then (if i.val < 1924 then (141, 242) else (70, 238)) else (if i.val < 1926 then (100, 103) else (139, 75))) else (if i.val < 1929 then (if i.val < 1928 then (117, 115) else (130, 95)) else (if i.val < 1930 then (144, 181) else (144, 127)))) else (if i.val < 1935 then (if i.val < 1933 then (if i.val < 1932 then (74, 92) else (117, 3)) else (if i.val < 1934 then (80, 213) else (91, 10))) else (if i.val < 1937 then (if i.val < 1936 then (64, 70) else (135, 17)) else (if i.val < 1938 then (143, 182) else (if i.val < 1939 then (137, 102) else (75, 139)))))) else (if i.val < 1948 then (if i.val < 1944 then (if i.val < 1942 then (if i.val < 1941 then (89, 190) else (135, 247)) else (if i.val < 1943 then (0, 18) else (137, 9))) else (if i.val < 1946 then (if i.val < 1945 then (142, 95) else (110, 236)) else (if i.val < 1947 then (116, 164) else (68, 39)))) else (if i.val < 1952 then (if i.val < 1950 then (if i.val < 1949 then (97, 198) else (71, 32)) else (if i.val < 1951 then (81, 152) else (100, 55))) else (if i.val < 1954 then (if i.val < 1953 then (65, 127) else (84, 109)) else (if i.val < 1955 then (133, 94) else (if i.val < 1956 then (142, 218) else (118, 60)))))))) else (if i.val < 1991 then (if i.val < 1974 then (if i.val < 1965 then (if i.val < 1961 then (if i.val < 1959 then (if i.val < 1958 then (140, 20) else (68, 25)) else (if i.val < 1960 then (34, 200) else (95, 37))) else (if i.val < 1963 then (if i.val < 1962 then (101, 227) else (105, 119)) else (if i.val < 1964 then (38, 23) else (141, 211)))) else (if i.val < 1969 then (if i.val < 1967 then (if i.val < 1966 then (90, 57) else (82, 128)) else (if i.val < 1968 then (73, 41) else (1, 215))) else (if i.val < 1971 then (if i.val < 1970 then (120, 130) else (108, 12)) else (if i.val < 1972 then (142, 13) else (if i.val < 1973 then (132, 95) else (111, 47)))))) else (if i.val < 1982 then (if i.val < 1978 then (if i.val < 1976 then (if i.val < 1975 then (73, 52) else (63, 79)) else (if i.val < 1977 then (52, 86) else (135, 202))) else (if i.val < 1980 then (if i.val < 1979 then (108, 123) else (95, 72)) else (if i.val < 1981 then (136, 143) else (87, 47)))) else (if i.val < 1986 then (if i.val < 1984 then (if i.val < 1983 then (140, 58) else (129, 229)) else (if i.val < 1985 then (136, 24) else (137, 248))) else (if i.val < 1988 then (if i.val < 1987 then (143, 129) else (144, 225)) else (if i.val < 1989 then (7, 158) else (if i.val < 1990 then (125, 246) else (135, 149))))))) else (if i.val < 2008 then (if i.val < 1999 then (if i.val < 1995 then (if i.val < 1993 then (if i.val < 1992 then (95, 179) else (130, 131)) else (if i.val < 1994 then (136, 27) else (142, 37))) else (if i.val < 1997 then (if i.val < 1996 then (74, 15) else (144, 159)) else (if i.val < 1998 then (114, 91) else (103, 234)))) else (if i.val < 2003 then (if i.val < 2001 then (if i.val < 2000 then (143, 172) else (142, 181)) else (if i.val < 2002 then (87, 84) else (17, 109))) else (if i.val < 2005 then (if i.val < 2004 then (43, 165) else (31, 122)) else (if i.val < 2006 then (36, 66) else (if i.val < 2007 then (46, 22) else (78, 149)))))) else (if i.val < 2016 then (if i.val < 2012 then (if i.val < 2010 then (if i.val < 2009 then (35, 217) else (79, 146)) else (if i.val < 2011 then (120, 38) else (132, 83))) else (if i.val < 2014 then (if i.val < 2013 then (55, 75) else (20, 168)) else (if i.val < 2015 then (64, 200) else (55, 205)))) else (if i.val < 2020 then (if i.val < 2018 then (if i.val < 2017 then (105, 123) else (140, 157)) else (if i.val < 2019 then (68, 186) else (45, 6))) else (if i.val < 2022 then (if i.val < 2021 then (58, 27) else (137, 212)) else (if i.val < 2023 then (114, 1) else (if i.val < 2024 then (45, 152) else (105, 169))))))))) else (if i.val < 2092 then (if i.val < 2058 then (if i.val < 2041 then (if i.val < 2033 then (if i.val < 2029 then (if i.val < 2027 then (if i.val < 2026 then (2, 142) else (23, 204)) else (if i.val < 2028 then (56, 106) else (22, 113))) else (if i.val < 2031 then (if i.val < 2030 then (46, 217) else (73, 32)) else (if i.val < 2032 then (102, 210) else (130, 40)))) else (if i.val < 2037 then (if i.val < 2035 then (if i.val < 2034 then (117, 112) else (70, 197)) else (if i.val < 2036 then (141, 179) else (53, 72))) else (if i.val < 2039 then (if i.val < 2038 then (111, 103) else (86, 95)) else (if i.val < 2040 then (137, 75) else (7, 244))))) else (if i.val < 2049 then (if i.val < 2045 then (if i.val < 2043 then (if i.val < 2042 then (35, 210) else (58, 142)) else (if i.val < 2044 then (91, 183) else (142, 89))) else (if i.val < 2047 then (if i.val < 2046 then (128, 66) else (46, 121)) else (if i.val < 2048 then (142, 201) else (131, 19)))) else (if i.val < 2053 then (if i.val < 2051 then (if i.val < 2050 then (0, 124) else (108, 152)) else (if i.val < 2052 then (84, 176) else (29, 49))) else (if i.val < 2055 then (if i.val < 2054 then (137, 158) else (128, 231)) else (if i.val < 2056 then (117, 125) else (if i.val < 2057 then (107, 21) else (58, 188))))))) else (if i.val < 2075 then (if i.val < 2066 then (if i.val < 2062 then (if i.val < 2060 then (if i.val < 2059 then (98, 12) else (139, 118)) else (if i.val < 2061 then (15, 1) else (120, 181))) else (if i.val < 2064 then (if i.val < 2063 then (136, 183) else (66, 39)) else (if i.val < 2065 then (137, 2) else (105, 179)))) else (if i.val < 2070 then (if i.val < 2068 then (if i.val < 2067 then (141, 208) else (14, 88)) else (if i.val < 2069 then (142, 66) else (85, 148))) else (if i.val < 2072 then (if i.val < 2071 then (127, 187) else (128, 65)) else (if i.val < 2073 then (77, 135) else (if i.val < 2074 then (108, 213) else (84, 218)))))) else (if i.val < 2083 then (if i.val < 2079 then (if i.val < 2077 then (if i.val < 2076 then (26, 7) else (137, 135)) else (if i.val < 2078 then (85, 26) else (46, 70))) else (if i.val < 2081 then (if i.val < 2080 then (9, 61) else (16, 101)) else (if i.val < 2082 then (111, 216) else (29, 168)))) else (if i.val < 2087 then (if i.val < 2085 then (if i.val < 2084 then (133, 10) else (127, 8)) else (if i.val < 2086 then (85, 114) else (144, 58))) else (if i.val < 2089 then (if i.val < 2088 then (53, 80) else (84, 192)) else (if i.val < 2090 then (105, 91) else (if i.val < 2091 then (142, 136) else (10, 25)))))))) else (if i.val < 2126 then (if i.val < 2109 then (if i.val < 2100 then (if i.val < 2096 then (if i.val < 2094 then (if i.val < 2093 then (104, 126) else (82, 255)) else (if i.val < 2095 then (110, 181) else (0, 37))) else (if i.val < 2098 then (if i.val < 2097 then (81, 218) else (12, 103)) else (if i.val < 2099 then (57, 68) else (7, 117)))) else (if i.val < 2104 then (if i.val < 2102 then (if i.val < 2101 then (116, 52) else (95, 6)) else (if i.val < 2103 then (3, 41) else (39, 40))) else (if i.val < 2106 then (if i.val < 2105 then (122, 52) else (131, 108)) else (if i.val < 2107 then (18, 86) else (if i.val < 2108 then (125, 205) else (33, 7)))))) else (if i.val < 2117 then (if i.val < 2113 then (if i.val < 2111 then (if i.val < 2110 then (26, 11) else (85, 194)) else (if i.val < 2112 then (98, 45) else (106, 213))) else (if i.val < 2115 then (if i.val < 2114 then (98, 252) else (119, 56)) else (if i.val < 2116 then (47, 166) else (142, 41)))) else (if i.val < 2121 then (if i.val < 2119 then (if i.val < 2118 then (133, 75) else (120, 59)) else (if i.val < 2120 then (2, 230) else (52, 84))) else (if i.val < 2123 then (if i.val < 2122 then (1, 60) else (130, 200)) else (if i.val < 2124 then (116, 136) else (if i.val < 2125 then (87, 85) else (116, 80))))))) else (if i.val < 2143 then (if i.val < 2134 then (if i.val < 2130 then (if i.val < 2128 then (if i.val < 2127 then (0, 11) else (105, 161)) else (if i.val < 2129 then (112, 108) else (141, 199))) else (if i.val < 2132 then (if i.val < 2131 then (118, 101) else (131, 76)) else (if i.val < 2133 then (112, 64) else (144, 35)))) else (if i.val < 2138 then (if i.val < 2136 then (if i.val < 2135 then (128, 125) else (66, 46)) else (if i.val < 2137 then (77, 71) else (39, 33))) else (if i.val < 2140 then (if i.val < 2139 then (8, 102) else (123, 254)) else (if i.val < 2141 then (111, 5) else (if i.val < 2142 then (89, 133) else (5, 240)))))) else (if i.val < 2151 then (if i.val < 2147 then (if i.val < 2145 then (if i.val < 2144 then (133, 1) else (144, 84)) else (if i.val < 2146 then (140, 103) else (104, 60))) else (if i.val < 2149 then (if i.val < 2148 then (115, 212) else (135, 175)) else (if i.val < 2150 then (106, 184) else (92, 100)))) else (if i.val < 2155 then (if i.val < 2153 then (if i.val < 2152 then (143, 204) else (126, 66)) else (if i.val < 2154 then (92, 187) else (110, 209))) else (if i.val < 2157 then (if i.val < 2156 then (78, 49) else (57, 231)) else (if i.val < 2158 then (116, 74) else (if i.val < 2159 then (113, 22) else (128, 56))))))))))))) else (if i.val < 3240 then (if i.val < 2700 then (if i.val < 2430 then (if i.val < 2295 then (if i.val < 2227 then (if i.val < 2193 then (if i.val < 2176 then (if i.val < 2168 then (if i.val < 2164 then (if i.val < 2162 then (if i.val < 2161 then (126, 135) else (144, 110)) else (if i.val < 2163 then (128, 3) else (1, 246))) else (if i.val < 2166 then (if i.val < 2165 then (122, 144) else (82, 184)) else (if i.val < 2167 then (12, 4) else (79, 73)))) else (if i.val < 2172 then (if i.val < 2170 then (if i.val < 2169 then (113, 2) else (144, 26)) else (if i.val < 2171 then (143, 30) else (32, 236))) else (if i.val < 2174 then (if i.val < 2173 then (111, 30) else (89, 160)) else (if i.val < 2175 then (128, 102) else (28, 85))))) else (if i.val < 2184 then (if i.val < 2180 then (if i.val < 2178 then (if i.val < 2177 then (22, 243) else (41, 38)) else (if i.val < 2179 then (34, 66) else (139, 25))) else (if i.val < 2182 then (if i.val < 2181 then (135, 60) else (33, 208)) else (if i.val < 2183 then (143, 5) else (113, 212)))) else (if i.val < 2188 then (if i.val < 2186 then (if i.val < 2185 then (50, 141) else (66, 146)) else (if i.val < 2187 then (101, 12) else (139, 54))) else (if i.val < 2190 then (if i.val < 2189 then (1, 85) else (102, 173)) else (if i.val < 2191 then (79, 245) else (if i.val < 2192 then (110, 64) else (116, 58))))))) else (if i.val < 2210 then (if i.val < 2201 then (if i.val < 2197 then (if i.val < 2195 then (if i.val < 2194 then (136, 148) else (131, 88)) else (if i.val < 2196 then (139, 224) else (71, 34))) else (if i.val < 2199 then (if i.val < 2198 then (51, 54) else (77, 245)) else (if i.val < 2200 then (10, 1) else (131, 50)))) else (if i.val < 2205 then (if i.val < 2203 then (if i.val < 2202 then (77, 191) else (84, 75)) else (if i.val < 2204 then (76, 53) else (112, 75))) else (if i.val < 2207 then (if i.val < 2206 then (83, 23) else (104, 51)) else (if i.val < 2208 then (139, 77) else (if i.val < 2209 then (21, 172) else (113, 8)))))) else (if i.val < 2218 then (if i.val < 2214 then (if i.val < 2212 then (if i.val < 2211 then (141, 28) else (60, 29)) else (if i.val < 2213 then (78, 56) else (106, 197))) else (if i.val < 2216 then (if i.val < 2215 then (93, 21) else (118, 255)) else (if i.val < 2217 then (120, 131) else (72, 195)))) else (if i.val < 2222 then (if i.val < 2220 then (if i.val < 2219 then (62, 76) else (128, 208)) else (if i.val < 2221 then (124, 68) else (20, 131))) else (if i.val < 2224 then (if i.val < 2223 then (105, 62) else (37, 185)) else (if i.val < 2225 then (4, 17) else (if i.val < 2226 then (122, 136) else (114, 36)))))))) else (if i.val < 2261 then (if i.val < 2244 then (if i.val < 2235 then (if i.val < 2231 then (if i.val < 2229 then (if i.val < 2228 then (127, 254) else (51, 63)) else (if i.val < 2230 then (132, 1) else (126, 227))) else (if i.val < 2233 then (if i.val < 2232 then (119, 174) else (110, 77)) else (if i.val < 2234 then (125, 210) else (104, 61)))) else (if i.val < 2239 then (if i.val < 2237 then (if i.val < 2236 then (125, 45) else (82, 153)) else (if i.val < 2238 then (124, 35) else (131, 197))) else (if i.val < 2241 then (if i.val < 2240 then (93, 32) else (116, 86)) else (if i.val < 2242 then (41, 219) else (if i.val < 2243 then (50, 110) else (39, 193)))))) else (if i.val < 2252 then (if i.val < 2248 then (if i.val < 2246 then (if i.val < 2245 then (122, 196) else (112, 232)) else (if i.val < 2247 then (120, 152) else (114, 203))) else (if i.val < 2250 then (if i.val < 2249 then (119, 244) else (43, 17)) else (if i.val < 2251 then (141, 90) else (72, 33)))) else (if i.val < 2256 then (if i.val < 2254 then (if i.val < 2253 then (81, 12) else (136, 219)) else (if i.val < 2255 then (59, 236) else (62, 168))) else (if i.val < 2258 then (if i.val < 2257 then (129, 16) else (120, 240)) else (if i.val < 2259 then (72, 243) else (if i.val < 2260 then (61, 249) else (138, 226))))))) else (if i.val < 2278 then (if i.val < 2269 then (if i.val < 2265 then (if i.val < 2263 then (if i.val < 2262 then (130, 110) else (80, 10)) else (if i.val < 2264 then (37, 51) else (144, 145))) else (if i.val < 2267 then (if i.val < 2266 then (99, 18) else (137, 157)) else (if i.val < 2268 then (106, 32) else (4, 77)))) else (if i.val < 2273 then (if i.val < 2271 then (if i.val < 2270 then (143, 237) else (18, 165)) else (if i.val < 2272 then (106, 146) else (134, 89))) else (if i.val < 2275 then (if i.val < 2274 then (80, 254) else (136, 100)) else (if i.val < 2276 then (114, 29) else (if i.val < 2277 then (104, 236) else (81, 248)))))) else (if i.val < 2286 then (if i.val < 2282 then (if i.val < 2280 then (if i.val < 2279 then (108, 251) else (141, 182)) else (if i.val < 2281 then (39, 197) else (112, 231))) else (if i.val < 2284 then (if i.val < 2283 then (124, 102) else (125, 13)) else (if i.val < 2285 then (103, 42) else (92, 31)))) else (if i.val < 2290 then (if i.val < 2288 then (if i.val < 2287 then (143, 189) else (116, 81)) else (if i.val < 2289 then (64, 227) else (4, 11))) else (if i.val < 2292 then (if i.val < 2291 then (12, 22) else (115, 241)) else (if i.val < 2293 then (139, 189) else (if i.val < 2294 then (119, 138) else (82, 253))))))))) else (if i.val < 2362 then (if i.val < 2328 then (if i.val < 2311 then (if i.val < 2303 then (if i.val < 2299 then (if i.val < 2297 then (if i.val < 2296 then (71, 65) else (85, 60)) else (if i.val < 2298 then (92, 16) else (144, 10))) else (if i.val < 2301 then (if i.val < 2300 then (15, 11) else (126, 107)) else (if i.val < 2302 then (29, 32) else (142, 74)))) else (if i.val < 2307 then (if i.val < 2305 then (if i.val < 2304 then (139, 43) else (23, 53)) else (if i.val < 2306 then (84, 93) else (36, 46))) else (if i.val < 2309 then (if i.val < 2308 then (125, 128) else (92, 176)) else (if i.val < 2310 then (112, 213) else (140, 70))))) else (if i.val < 2319 then (if i.val < 2315 then (if i.val < 2313 then (if i.val < 2312 then (66, 51) else (17, 208)) else (if i.val < 2314 then (113, 109) else (32, 95))) else (if i.val < 2317 then (if i.val < 2316 then (143, 52) else (81, 242)) else (if i.val < 2318 then (72, 2) else (112, 51)))) else (if i.val < 2323 then (if i.val < 2321 then (if i.val < 2320 then (97, 246) else (58, 113)) else (if i.val < 2322 then (142, 186) else (118, 110))) else (if i.val < 2325 then (if i.val < 2324 then (117, 79) else (69, 172)) else (if i.val < 2326 then (136, 137) else (if i.val < 2327 then (67, 120) else (120, 205))))))) else (if i.val < 2345 then (if i.val < 2336 then (if i.val < 2332 then (if i.val < 2330 then (if i.val < 2329 then (75, 29) else (139, 8)) else (if i.val < 2331 then (124, 168) else (20, 185))) else (if i.val < 2334 then (if i.val < 2333 then (102, 237) else (118, 105)) else (if i.val < 2335 then (48, 21) else (138, 76)))) else (if i.val < 2340 then (if i.val < 2338 then (if i.val < 2337 then (36, 176) else (133, 211)) else (if i.val < 2339 then (120, 26) else (85, 236))) else (if i.val < 2342 then (if i.val < 2341 then (130, 43) else (113, 87)) else (if i.val < 2343 then (15, 182) else (if i.val < 2344 then (104, 135) else (13, 18)))))) else (if i.val < 2353 then (if i.val < 2349 then (if i.val < 2347 then (if i.val < 2346 then (117, 209) else (128, 59)) else (if i.val < 2348 then (65, 98) else (134, 216))) else (if i.val < 2351 then (if i.val < 2350 then (137, 222) else (134, 115)) else (if i.val < 2352 then (115, 176) else (30, 174)))) else (if i.val < 2357 then (if i.val < 2355 then (if i.val < 2354 then (118, 247) else (15, 67)) else (if i.val < 2356 then (144, 156) else (126, 108))) else (if i.val < 2359 then (if i.val < 2358 then (116, 131) else (103, 125)) else (if i.val < 2360 then (131, 83) else (if i.val < 2361 then (139, 87) else (32, 177)))))))) else (if i.val < 2396 then (if i.val < 2379 then (if i.val < 2370 then (if i.val < 2366 then (if i.val < 2364 then (if i.val < 2363 then (139, 132) else (76, 170)) else (if i.val < 2365 then (81, 163) else (64, 195))) else (if i.val < 2368 then (if i.val < 2367 then (141, 105) else (36, 97)) else (if i.val < 2369 then (144, 214) else (142, 163)))) else (if i.val < 2374 then (if i.val < 2372 then (if i.val < 2371 then (48, 197) else (135, 14)) else (if i.val < 2373 then (67, 27) else (117, 245))) else (if i.val < 2376 then (if i.val < 2375 then (67, 9) else (101, 228)) else (if i.val < 2377 then (40, 73) else (if i.val < 2378 then (124, 193) else (54, 153)))))) else (if i.val < 2387 then (if i.val < 2383 then (if i.val < 2381 then (if i.val < 2380 then (57, 131) else (143, 255)) else (if i.val < 2382 then (138, 232) else (132, 39))) else (if i.val < 2385 then (if i.val < 2384 then (74, 102) else (94, 19)) else (if i.val < 2386 then (130, 168) else (112, 43)))) else (if i.val < 2391 then (if i.val < 2389 then (if i.val < 2388 then (116, 234) else (112, 187)) else (if i.val < 2390 then (68, 219) else (120, 7))) else (if i.val < 2393 then (if i.val < 2392 then (88, 80) else (50, 153)) else (if i.val < 2394 then (112, 128) else (if i.val < 2395 then (144, 109) else (17, 17))))))) else (if i.val < 2413 then (if i.val < 2404 then (if i.val < 2400 then (if i.val < 2398 then (if i.val < 2397 then (9, 75) else (83, 92)) else (if i.val < 2399 then (73, 131) else (130, 235))) else (if i.val < 2402 then (if i.val < 2401 then (105, 218) else (135, 170)) else (if i.val < 2403 then (98, 23) else (104, 89)))) else (if i.val < 2408 then (if i.val < 2406 then (if i.val < 2405 then (114, 202) else (95, 191)) else (if i.val < 2407 then (85, 89) else (56, 202))) else (if i.val < 2410 then (if i.val < 2409 then (144, 15) else (39, 195)) else (if i.val < 2411 then (143, 20) else (if i.val < 2412 then (26, 32) else (131, 150)))))) else (if i.val < 2421 then (if i.val < 2417 then (if i.val < 2415 then (if i.val < 2414 then (94, 118) else (53, 105)) else (if i.val < 2416 then (144, 103) else (58, 204))) else (if i.val < 2419 then (if i.val < 2418 then (48, 96) else (23, 46)) else (if i.val < 2420 then (135, 73) else (131, 44)))) else (if i.val < 2425 then (if i.val < 2423 then (if i.val < 2422 then (79, 175) else (127, 88)) else (if i.val < 2424 then (67, 38) else (76, 225))) else (if i.val < 2427 then (if i.val < 2426 then (54, 89) else (41, 216)) else (if i.val < 2428 then (128, 94) else (if i.val < 2429 then (137, 47) else (73, 9)))))))))) else (if i.val < 2565 then (if i.val < 2497 then (if i.val < 2463 then (if i.val < 2446 then (if i.val < 2438 then (if i.val < 2434 then (if i.val < 2432 then (if i.val < 2431 then (127, 99) else (9, 207)) else (if i.val < 2433 then (137, 207) else (50, 246))) else (if i.val < 2436 then (if i.val < 2435 then (90, 103) else (92, 173)) else (if i.val < 2437 then (133, 87) else (10, 249)))) else (if i.val < 2442 then (if i.val < 2440 then (if i.val < 2439 then (143, 78) else (28, 196)) else (if i.val < 2441 then (14, 36) else (73, 22))) else (if i.val < 2444 then (if i.val < 2443 then (89, 223) else (92, 40)) else (if i.val < 2445 then (68, 169) else (122, 113))))) else (if i.val < 2454 then (if i.val < 2450 then (if i.val < 2448 then (if i.val < 2447 then (112, 158) else (11, 23)) else (if i.val < 2449 then (121, 44) else (32, 216))) else (if i.val < 2452 then (if i.val < 2451 then (47, 218) else (85, 192)) else (if i.val < 2453 then (25, 160) else (102, 235)))) else (if i.val < 2458 then (if i.val < 2456 then (if i.val < 2455 then (54, 209) else (132, 231)) else (if i.val < 2457 then (141, 43) else (101, 130))) else (if i.val < 2460 then (if i.val < 2459 then (138, 187) else (89, 108)) else (if i.val < 2461 then (83, 108) else (if i.val < 2462 then (122, 177) else (97, 82))))))) else (if i.val < 2480 then (if i.val < 2471 then (if i.val < 2467 then (if i.val < 2465 then (if i.val < 2464 then (129, 111) else (71, 125)) else (if i.val < 2466 then (91, 179) else (47, 97))) else (if i.val < 2469 then (if i.val < 2468 then (114, 195) else (119, 247)) else (if i.val < 2470 then (33, 245) else (142, 210)))) else (if i.val < 2475 then (if i.val < 2473 then (if i.val < 2472 then (109, 178) else (138, 173)) else (if i.val < 2474 then (57, 59) else (78, 139))) else (if i.val < 2477 then (if i.val < 2476 then (53, 77) else (6, 144)) else (if i.val < 2478 then (65, 21) else (if i.val < 2479 then (134, 206) else (114, 236)))))) else (if i.val < 2488 then (if i.val < 2484 then (if i.val < 2482 then (if i.val < 2481 then (90, 173) else (51, 26)) else (if i.val < 2483 then (49, 112) else (42, 181))) else (if i.val < 2486 then (if i.val < 2485 then (141, 44) else (98, 85)) else (if i.val < 2487 then (60, 71) else (127, 150)))) else (if i.val < 2492 then (if i.val < 2490 then (if i.val < 2489 then (82, 241) else (65, 144)) else (if i.val < 2491 then (67, 81) else (112, 191))) else (if i.val < 2494 then (if i.val < 2493 then (98, 208) else (132, 118)) else (if i.val < 2495 then (10, 145) else (if i.val < 2496 then (73, 244) else (110, 15)))))))) else (if i.val < 2531 then (if i.val < 2514 then (if i.val < 2505 then (if i.val < 2501 then (if i.val < 2499 then (if i.val < 2498 then (137, 148) else (126, 3)) else (if i.val < 2500 then (135, 71) else (116, 91))) else (if i.val < 2503 then (if i.val < 2502 then (88, 75) else (65, 119)) else (if i.val < 2504 then (142, 7) else (63, 209)))) else (if i.val < 2509 then (if i.val < 2507 then (if i.val < 2506 then (60, 224) else (134, 252)) else (if i.val < 2508 then (13, 47) else (6, 222))) else (if i.val < 2511 then (if i.val < 2510 then (119, 93) else (141, 189)) else (if i.val < 2512 then (132, 127) else (if i.val < 2513 then (90, 219) else (134, 192)))))) else (if i.val < 2522 then (if i.val < 2518 then (if i.val < 2516 then (if i.val < 2515 then (86, 174) else (123, 60)) else (if i.val < 2517 then (9, 217) else (138, 158))) else (if i.val < 2520 then (if i.val < 2519 then (116, 0) else (83, 115)) else (if i.val < 2521 then (135, 85) else (143, 141)))) else (if i.val < 2526 then (if i.val < 2524 then (if i.val < 2523 then (111, 59) else (105, 182)) else (if i.val < 2525 then (93, 50) else (124, 191))) else (if i.val < 2528 then (if i.val < 2527 then (97, 106) else (138, 151)) else (if i.val < 2529 then (125, 252) else (if i.val < 2530 then (14, 254) else (55, 148))))))) else (if i.val < 2548 then (if i.val < 2539 then (if i.val < 2535 then (if i.val < 2533 then (if i.val < 2532 then (130, 254) else (117, 231)) else (if i.val < 2534 then (68, 103) else (98, 231))) else (if i.val < 2537 then (if i.val < 2536 then (133, 198) else (120, 92)) else (if i.val < 2538 then (116, 182) else (53, 143)))) else (if i.val < 2543 then (if i.val < 2541 then (if i.val < 2540 then (113, 162) else (28, 247)) else (if i.val < 2542 then (49, 236) else (119, 65))) else (if i.val < 2545 then (if i.val < 2544 then (126, 70) else (132, 86)) else (if i.val < 2546 then (129, 28) else (if i.val < 2547 then (43, 92) else (11, 179)))))) else (if i.val < 2556 then (if i.val < 2552 then (if i.val < 2550 then (if i.val < 2549 then (123, 202) else (20, 198)) else (if i.val < 2551 then (130, 30) else (144, 116))) else (if i.val < 2554 then (if i.val < 2553 then (143, 75) else (100, 255)) else (if i.val < 2555 then (123, 73) else (133, 91)))) else (if i.val < 2560 then (if i.val < 2558 then (if i.val < 2557 then (97, 114) else (142, 64)) else (if i.val < 2559 then (87, 222) else (3, 162))) else (if i.val < 2562 then (if i.val < 2561 then (93, 42) else (82, 58)) else (if i.val < 2563 then (123, 147) else (if i.val < 2564 then (17, 123) else (70, 54))))))))) else (if i.val < 2632 then (if i.val < 2598 then (if i.val < 2581 then (if i.val < 2573 then (if i.val < 2569 then (if i.val < 2567 then (if i.val < 2566 then (87, 69) else (47, 130)) else (if i.val < 2568 then (86, 0) else (40, 66))) else (if i.val < 2571 then (if i.val < 2570 then (137, 210) else (139, 213)) else (if i.val < 2572 then (116, 17) else (57, 167)))) else (if i.val < 2577 then (if i.val < 2575 then (if i.val < 2574 then (6, 157) else (63, 1)) else (if i.val < 2576 then (135, 141) else (132, 210))) else (if i.val < 2579 then (if i.val < 2578 then (70, 162) else (62, 221)) else (if i.val < 2580 then (97, 153) else (28, 67))))) else (if i.val < 2589 then (if i.val < 2585 then (if i.val < 2583 then (if i.val < 2582 then (64, 184) else (80, 253)) else (if i.val < 2584 then (112, 12) else (114, 170))) else (if i.val < 2587 then (if i.val < 2586 then (129, 173) else (103, 168)) else (if i.val < 2588 then (75, 98) else (78, 156)))) else (if i.val < 2593 then (if i.val < 2591 then (if i.val < 2590 then (141, 217) else (21, 76)) else (if i.val < 2592 then (131, 112) else (129, 27))) else (if i.val < 2595 then (if i.val < 2594 then (133, 248) else (52, 119)) else (if i.val < 2596 then (121, 109) else (if i.val < 2597 then (134, 243) else (126, 103))))))) else (if i.val < 2615 then (if i.val < 2606 then (if i.val < 2602 then (if i.val < 2600 then (if i.val < 2599 then (33, 53) else (95, 178)) else (if i.val < 2601 then (110, 61) else (140, 46))) else (if i.val < 2604 then (if i.val < 2603 then (140, 177) else (96, 148)) else (if i.val < 2605 then (137, 206) else (119, 72)))) else (if i.val < 2610 then (if i.val < 2608 then (if i.val < 2607 then (57, 205) else (6, 166)) else (if i.val < 2609 then (40, 151) else (66, 119))) else (if i.val < 2612 then (if i.val < 2611 then (124, 101) else (144, 171)) else (if i.val < 2613 then (38, 198) else (if i.val < 2614 then (72, 216) else (134, 119)))))) else (if i.val < 2623 then (if i.val < 2619 then (if i.val < 2617 then (if i.val < 2616 then (139, 67) else (129, 72)) else (if i.val < 2618 then (38, 222) else (122, 187))) else (if i.val < 2621 then (if i.val < 2620 then (125, 156) else (65, 40)) else (if i.val < 2622 then (134, 28) else (143, 31)))) else (if i.val < 2627 then (if i.val < 2625 then (if i.val < 2624 then (103, 68) else (67, 155)) else (if i.val < 2626 then (132, 42) else (87, 210))) else (if i.val < 2629 then (if i.val < 2628 then (144, 18) else (50, 172)) else (if i.val < 2630 then (100, 85) else (if i.val < 2631 then (76, 56) else (124, 251)))))))) else (if i.val < 2666 then (if i.val < 2649 then (if i.val < 2640 then (if i.val < 2636 then (if i.val < 2634 then (if i.val < 2633 then (51, 158) else (73, 243)) else (if i.val < 2635 then (141, 218) else (104, 109))) else (if i.val < 2638 then (if i.val < 2637 then (137, 39) else (134, 235)) else (if i.val < 2639 then (59, 102) else (87, 5)))) else (if i.val < 2644 then (if i.val < 2642 then (if i.val < 2641 then (39, 57) else (124, 29)) else (if i.val < 2643 then (62, 16) else (136, 239))) else (if i.val < 2646 then (if i.val < 2645 then (40, 107) else (123, 91)) else (if i.val < 2647 then (15, 184) else (if i.val < 2648 then (107, 84) else (43, 205)))))) else (if i.val < 2657 then (if i.val < 2653 then (if i.val < 2651 then (if i.val < 2650 then (16, 34) else (138, 123)) else (if i.val < 2652 then (131, 10) else (93, 237))) else (if i.val < 2655 then (if i.val < 2654 then (95, 20) else (118, 220)) else (if i.val < 2656 then (124, 130) else (65, 139)))) else (if i.val < 2661 then (if i.val < 2659 then (if i.val < 2658 then (99, 161) else (100, 197)) else (if i.val < 2660 then (137, 58) else (62, 19))) else (if i.val < 2663 then (if i.val < 2662 then (141, 49) else (98, 238)) else (if i.val < 2664 then (140, 142) else (if i.val < 2665 then (69, 190) else (18, 33))))))) else (if i.val < 2683 then (if i.val < 2674 then (if i.val < 2670 then (if i.val < 2668 then (if i.val < 2667 then (69, 213) else (114, 252)) else (if i.val < 2669 then (102, 76) else (75, 167))) else (if i.val < 2672 then (if i.val < 2671 then (103, 207) else (36, 220)) else (if i.val < 2673 then (11, 127) else (19, 110)))) else (if i.val < 2678 then (if i.val < 2676 then (if i.val < 2675 then (96, 94) else (30, 146)) else (if i.val < 2677 then (58, 70) else (138, 216))) else (if i.val < 2680 then (if i.val < 2679 then (135, 110) else (141, 244)) else (if i.val < 2681 then (135, 177) else (if i.val < 2682 then (93, 113) else (30, 124)))))) else (if i.val < 2691 then (if i.val < 2687 then (if i.val < 2685 then (if i.val < 2684 then (139, 79) else (132, 252)) else (if i.val < 2686 then (126, 181) else (6, 253))) else (if i.val < 2689 then (if i.val < 2688 then (142, 178) else (86, 134)) else (if i.val < 2690 then (123, 48) else (6, 107)))) else (if i.val < 2695 then (if i.val < 2693 then (if i.val < 2692 then (139, 199) else (120, 64)) else (if i.val < 2694 then (139, 147) else (143, 95))) else (if i.val < 2697 then (if i.val < 2696 then (71, 41) else (83, 44)) else (if i.val < 2698 then (137, 199) else (if i.val < 2699 then (123, 33) else (121, 88))))))))))) else (if i.val < 2970 then (if i.val < 2835 then (if i.val < 2767 then (if i.val < 2733 then (if i.val < 2716 then (if i.val < 2708 then (if i.val < 2704 then (if i.val < 2702 then (if i.val < 2701 then (144, 197) else (132, 16)) else (if i.val < 2703 then (95, 24) else (143, 244))) else (if i.val < 2706 then (if i.val < 2705 then (135, 88) else (138, 4)) else (if i.val < 2707 then (141, 106) else (123, 165)))) else (if i.val < 2712 then (if i.val < 2710 then (if i.val < 2709 then (36, 13) else (126, 196)) else (if i.val < 2711 then (58, 100) else (78, 231))) else (if i.val < 2714 then (if i.val < 2713 then (42, 235) else (130, 106)) else (if i.val < 2715 then (27, 138) else (14, 54))))) else (if i.val < 2724 then (if i.val < 2720 then (if i.val < 2718 then (if i.val < 2717 then (74, 169) else (68, 130)) else (if i.val < 2719 then (133, 80) else (73, 226))) else (if i.val < 2722 then (if i.val < 2721 then (143, 186) else (75, 152)) else (if i.val < 2723 then (67, 211) else (127, 17)))) else (if i.val < 2728 then (if i.val < 2726 then (if i.val < 2725 then (112, 130) else (30, 0)) else (if i.val < 2727 then (100, 236) else (54, 215))) else (if i.val < 2730 then (if i.val < 2729 then (33, 206) else (98, 215)) else (if i.val < 2731 then (121, 116) else (if i.val < 2732 then (134, 45) else (137, 197))))))) else (if i.val < 2750 then (if i.val < 2741 then (if i.val < 2737 then (if i.val < 2735 then (if i.val < 2734 then (91, 253) else (128, 202)) else (if i.val < 2736 then (71, 166) else (126, 52))) else (if i.val < 2739 then (if i.val < 2738 then (40, 71) else (139, 10)) else (if i.val < 2740 then (142, 54) else (116, 8)))) else (if i.val < 2745 then (if i.val < 2743 then (if i.val < 2742 then (144, 115) else (21, 156)) else (if i.val < 2744 then (123, 192) else (90, 71))) else (if i.val < 2747 then (if i.val < 2746 then (131, 204) else (132, 196)) else (if i.val < 2748 then (122, 22) else (if i.val < 2749 then (105, 237) else (132, 18)))))) else (if i.val < 2758 then (if i.val < 2754 then (if i.val < 2752 then (if i.val < 2751 then (138, 60) else (84, 78)) else (if i.val < 2753 then (97, 144) else (18, 176))) else (if i.val < 2756 then (if i.val < 2755 then (15, 229) else (5, 158)) else (if i.val < 2757 then (102, 249) else (132, 13)))) else (if i.val < 2762 then (if i.val < 2760 then (if i.val < 2759 then (121, 172) else (134, 30)) else (if i.val < 2761 then (66, 197) else (119, 128))) else (if i.val < 2764 then (if i.val < 2763 then (87, 50) else (125, 232)) else (if i.val < 2765 then (120, 224) else (if i.val < 2766 then (89, 179) else (37, 236)))))))) else (if i.val < 2801 then (if i.val < 2784 then (if i.val < 2775 then (if i.val < 2771 then (if i.val < 2769 then (if i.val < 2768 then (56, 126) else (34, 106)) else (if i.val < 2770 then (125, 22) else (94, 54))) else (if i.val < 2773 then (if i.val < 2772 then (141, 112) else (118, 92)) else (if i.val < 2774 then (87, 55) else (89, 192)))) else (if i.val < 2779 then (if i.val < 2777 then (if i.val < 2776 then (54, 57) else (113, 245)) else (if i.val < 2778 then (74, 29) else (106, 28))) else (if i.val < 2781 then (if i.val < 2780 then (110, 53) else (89, 231)) else (if i.val < 2782 then (126, 232) else (if i.val < 2783 then (119, 200) else (76, 36)))))) else (if i.val < 2792 then (if i.val < 2788 then (if i.val < 2786 then (if i.val < 2785 then (141, 113) else (134, 91)) else (if i.val < 2787 then (125, 95) else (42, 149))) else (if i.val < 2790 then (if i.val < 2789 then (69, 58) else (87, 32)) else (if i.val < 2791 then (140, 72) else (131, 228)))) else (if i.val < 2796 then (if i.val < 2794 then (if i.val < 2793 then (106, 114) else (118, 6)) else (if i.val < 2795 then (128, 87) else (114, 55))) else (if i.val < 2798 then (if i.val < 2797 then (64, 110) else (119, 104)) else (if i.val < 2799 then (14, 146) else (if i.val < 2800 then (132, 37) else (130, 92))))))) else (if i.val < 2818 then (if i.val < 2809 then (if i.val < 2805 then (if i.val < 2803 then (if i.val < 2802 then (141, 172) else (20, 72)) else (if i.val < 2804 then (139, 209) else (54, 61))) else (if i.val < 2807 then (if i.val < 2806 then (41, 18) else (67, 118)) else (if i.val < 2808 then (39, 116) else (23, 8)))) else (if i.val < 2813 then (if i.val < 2811 then (if i.val < 2810 then (143, 198) else (76, 198)) else (if i.val < 2812 then (37, 205) else (10, 210))) else (if i.val < 2815 then (if i.val < 2814 then (141, 23) else (98, 26)) else (if i.val < 2816 then (94, 89) else (if i.val < 2817 then (121, 211) else (137, 249)))))) else (if i.val < 2826 then (if i.val < 2822 then (if i.val < 2820 then (if i.val < 2819 then (74, 104) else (97, 4)) else (if i.val < 2821 then (144, 124) else (121, 190))) else (if i.val < 2824 then (if i.val < 2823 then (75, 104) else (61, 121)) else (if i.val < 2825 then (140, 209) else (114, 78)))) else (if i.val < 2830 then (if i.val < 2828 then (if i.val < 2827 then (122, 219) else (87, 98)) else (if i.val < 2829 then (144, 38) else (78, 181))) else (if i.val < 2832 then (if i.val < 2831 then (109, 198) else (3, 219)) else (if i.val < 2833 then (142, 230) else (if i.val < 2834 then (90, 114) else (121, 160))))))))) else (if i.val < 2902 then (if i.val < 2868 then (if i.val < 2851 then (if i.val < 2843 then (if i.val < 2839 then (if i.val < 2837 then (if i.val < 2836 then (37, 21) else (128, 97)) else (if i.val < 2838 then (41, 158) else (72, 171))) else (if i.val < 2841 then (if i.val < 2840 then (143, 212) else (124, 223)) else (if i.val < 2842 then (142, 12) else (74, 56)))) else (if i.val < 2847 then (if i.val < 2845 then (if i.val < 2844 then (53, 245) else (143, 112)) else (if i.val < 2846 then (132, 219) else (111, 146))) else (if i.val < 2849 then (if i.val < 2848 then (130, 119) else (110, 170)) else (if i.val < 2850 then (89, 104) else (100, 106))))) else (if i.val < 2859 then (if i.val < 2855 then (if i.val < 2853 then (if i.val < 2852 then (120, 252) else (139, 144)) else (if i.val < 2854 then (67, 165) else (45, 188))) else (if i.val < 2857 then (if i.val < 2856 then (140, 92) else (27, 0)) else (if i.val < 2858 then (34, 233) else (75, 207)))) else (if i.val < 2863 then (if i.val < 2861 then (if i.val < 2860 then (96, 125) else (135, 126)) else (if i.val < 2862 then (144, 216) else (30, 167))) else (if i.val < 2865 then (if i.val < 2864 then (122, 181) else (136, 193)) else (if i.val < 2866 then (133, 214) else (if i.val < 2867 then (88, 225) else (80, 71))))))) else (if i.val < 2885 then (if i.val < 2876 then (if i.val < 2872 then (if i.val < 2870 then (if i.val < 2869 then (143, 29) else (143, 245)) else (if i.val < 2871 then (130, 202) else (38, 60))) else (if i.val < 2874 then (if i.val < 2873 then (131, 198) else (137, 51)) else (if i.val < 2875 then (91, 99) else (138, 204)))) else (if i.val < 2880 then (if i.val < 2878 then (if i.val < 2877 then (108, 20) else (138, 77)) else (if i.val < 2879 then (91, 141) else (126, 234))) else (if i.val < 2882 then (if i.val < 2881 then (140, 68) else (94, 30)) else (if i.val < 2883 then (89, 182) else (if i.val < 2884 then (99, 247) else (61, 95)))))) else (if i.val < 2893 then (if i.val < 2889 then (if i.val < 2887 then (if i.val < 2886 then (51, 112) else (67, 142)) else (if i.val < 2888 then (100, 212) else (83, 66))) else (if i.val < 2891 then (if i.val < 2890 then (76, 99) else (21, 60)) else (if i.val < 2892 then (92, 39) else (99, 252)))) else (if i.val < 2897 then (if i.val < 2895 then (if i.val < 2894 then (123, 122) else (102, 234)) else (if i.val < 2896 then (35, 107) else (55, 137))) else (if i.val < 2899 then (if i.val < 2898 then (137, 149) else (123, 104)) else (if i.val < 2900 then (114, 204) else (if i.val < 2901 then (9, 165) else (95, 152)))))))) else (if i.val < 2936 then (if i.val < 2919 then (if i.val < 2910 then (if i.val < 2906 then (if i.val < 2904 then (if i.val < 2903 then (66, 44) else (132, 225)) else (if i.val < 2905 then (128, 148) else (98, 195))) else (if i.val < 2908 then (if i.val < 2907 then (124, 27) else (142, 101)) else (if i.val < 2909 then (87, 155) else (68, 114)))) else (if i.val < 2914 then (if i.val < 2912 then (if i.val < 2911 then (135, 2) else (117, 24)) else (if i.val < 2913 then (138, 185) else (125, 10))) else (if i.val < 2916 then (if i.val < 2915 then (46, 64) else (138, 217)) else (if i.val < 2917 then (107, 32) else (if i.val < 2918 then (135, 70) else (112, 14)))))) else (if i.val < 2927 then (if i.val < 2923 then (if i.val < 2921 then (if i.val < 2920 then (69, 56) else (58, 122)) else (if i.val < 2922 then (80, 246) else (43, 204))) else (if i.val < 2925 then (if i.val < 2924 then (62, 70) else (124, 248)) else (if i.val < 2926 then (79, 213) else (121, 224)))) else (if i.val < 2931 then (if i.val < 2929 then (if i.val < 2928 then (60, 94) else (61, 86)) else (if i.val < 2930 then (15, 141) else (108, 51))) else (if i.val < 2933 then (if i.val < 2932 then (143, 135) else (139, 45)) else (if i.val < 2934 then (144, 87) else (if i.val < 2935 then (139, 182) else (71, 169))))))) else (if i.val < 2953 then (if i.val < 2944 then (if i.val < 2940 then (if i.val < 2938 then (if i.val < 2937 then (139, 159) else (144, 45)) else (if i.val < 2939 then (92, 230) else (139, 168))) else (if i.val < 2942 then (if i.val < 2941 then (129, 56) else (22, 77)) else (if i.val < 2943 then (141, 13) else (115, 76)))) else (if i.val < 2948 then (if i.val < 2946 then (if i.val < 2945 then (43, 54) else (130, 104)) else (if i.val < 2947 then (116, 90) else (141, 247))) else (if i.val < 2950 then (if i.val < 2949 then (100, 92) else (141, 177)) else (if i.val < 2951 then (143, 72) else (if i.val < 2952 then (44, 213) else (120, 67)))))) else (if i.val < 2961 then (if i.val < 2957 then (if i.val < 2955 then (if i.val < 2954 then (137, 35) else (91, 13)) else (if i.val < 2956 then (51, 114) else (137, 121))) else (if i.val < 2959 then (if i.val < 2958 then (80, 34) else (2, 5)) else (if i.val < 2960 then (139, 30) else (109, 225)))) else (if i.val < 2965 then (if i.val < 2963 then (if i.val < 2962 then (137, 61) else (67, 124)) else (if i.val < 2964 then (25, 204) else (144, 140))) else (if i.val < 2967 then (if i.val < 2966 then (141, 148) else (15, 83)) else (if i.val < 2968 then (67, 182) else (if i.val < 2969 then (107, 135) else (31, 53)))))))))) else (if i.val < 3105 then (if i.val < 3037 then (if i.val < 3003 then (if i.val < 2986 then (if i.val < 2978 then (if i.val < 2974 then (if i.val < 2972 then (if i.val < 2971 then (109, 119) else (133, 245)) else (if i.val < 2973 then (61, 14) else (138, 26))) else (if i.val < 2976 then (if i.val < 2975 then (64, 65) else (79, 205)) else (if i.val < 2977 then (29, 71) else (97, 41)))) else (if i.val < 2982 then (if i.val < 2980 then (if i.val < 2979 then (106, 209) else (140, 17)) else (if i.val < 2981 then (39, 16) else (134, 6))) else (if i.val < 2984 then (if i.val < 2983 then (136, 29) else (123, 116)) else (if i.val < 2985 then (139, 11) else (96, 227))))) else (if i.val < 2994 then (if i.val < 2990 then (if i.val < 2988 then (if i.val < 2987 then (126, 217) else (86, 157)) else (if i.val < 2989 then (43, 173) else (127, 228))) else (if i.val < 2992 then (if i.val < 2991 then (86, 137) else (124, 57)) else (if i.val < 2993 then (125, 178) else (77, 4)))) else (if i.val < 2998 then (if i.val < 2996 then (if i.val < 2995 then (34, 155) else (70, 157)) else (if i.val < 2997 then (140, 233) else (134, 58))) else (if i.val < 3000 then (if i.val < 2999 then (119, 67) else (122, 72)) else (if i.val < 3001 then (142, 147) else (if i.val < 3002 then (41, 250) else (37, 77))))))) else (if i.val < 3020 then (if i.val < 3011 then (if i.val < 3007 then (if i.val < 3005 then (if i.val < 3004 then (29, 41) else (126, 233)) else (if i.val < 3006 then (143, 70) else (126, 171))) else (if i.val < 3009 then (if i.val < 3008 then (112, 27) else (72, 28)) else (if i.val < 3010 then (144, 169) else (60, 80)))) else (if i.val < 3015 then (if i.val < 3013 then (if i.val < 3012 then (115, 30) else (129, 134)) else (if i.val < 3014 then (136, 163) else (125, 192))) else (if i.val < 3017 then (if i.val < 3016 then (109, 149) else (77, 2)) else (if i.val < 3018 then (28, 166) else (if i.val < 3019 then (41, 5) else (140, 87)))))) else (if i.val < 3028 then (if i.val < 3024 then (if i.val < 3022 then (if i.val < 3021 then (57, 96) else (142, 191)) else (if i.val < 3023 then (136, 66) else (101, 96))) else (if i.val < 3026 then (if i.val < 3025 then (111, 234) else (113, 5)) else (if i.val < 3027 then (143, 158) else (109, 28)))) else (if i.val < 3032 then (if i.val < 3030 then (if i.val < 3029 then (129, 139) else (143, 188)) else (if i.val < 3031 then (31, 95) else (112, 147))) else (if i.val < 3034 then (if i.val < 3033 then (56, 94) else (75, 27)) else (if i.val < 3035 then (122, 153) else (if i.val < 3036 then (101, 194) else (142, 165)))))))) else (if i.val < 3071 then (if i.val < 3054 then (if i.val < 3045 then (if i.val < 3041 then (if i.val < 3039 then (if i.val < 3038 then (130, 253) else (139, 84)) else (if i.val < 3040 then (104, 161) else (129, 92))) else (if i.val < 3043 then (if i.val < 3042 then (99, 58) else (133, 13)) else (if i.val < 3044 then (142, 142) else (115, 99)))) else (if i.val < 3049 then (if i.val < 3047 then (if i.val < 3046 then (141, 91) else (85, 168)) else (if i.val < 3048 then (83, 119) else (75, 192))) else (if i.val < 3051 then (if i.val < 3050 then (116, 188) else (78, 25)) else (if i.val < 3052 then (81, 241) else (if i.val < 3053 then (138, 46) else (127, 225)))))) else (if i.val < 3062 then (if i.val < 3058 then (if i.val < 3056 then (if i.val < 3055 then (43, 37) else (56, 75)) else (if i.val < 3057 then (76, 157) else (144, 24))) else (if i.val < 3060 then (if i.val < 3059 then (140, 0) else (128, 222)) else (if i.val < 3061 then (135, 62) else (91, 53)))) else (if i.val < 3066 then (if i.val < 3064 then (if i.val < 3063 then (132, 20) else (82, 9)) else (if i.val < 3065 then (110, 123) else (95, 150))) else (if i.val < 3068 then (if i.val < 3067 then (138, 9) else (136, 71)) else (if i.val < 3069 then (111, 133) else (if i.val < 3070 then (90, 158) else (133, 146))))))) else (if i.val < 3088 then (if i.val < 3079 then (if i.val < 3075 then (if i.val < 3073 then (if i.val < 3072 then (122, 38) else (106, 141)) else (if i.val < 3074 then (133, 64) else (70, 109))) else (if i.val < 3077 then (if i.val < 3076 then (112, 118) else (124, 114)) else (if i.val < 3078 then (9, 49) else (54, 134)))) else (if i.val < 3083 then (if i.val < 3081 then (if i.val < 3080 then (136, 152) else (77, 73)) else (if i.val < 3082 then (86, 41) else (135, 183))) else (if i.val < 3085 then (if i.val < 3084 then (8, 155) else (133, 95)) else (if i.val < 3086 then (117, 248) else (if i.val < 3087 then (58, 207) else (29, 175)))))) else (if i.val < 3096 then (if i.val < 3092 then (if i.val < 3090 then (if i.val < 3089 then (111, 138) else (143, 84)) else (if i.val < 3091 then (92, 237) else (80, 113))) else (if i.val < 3094 then (if i.val < 3093 then (66, 157) else (64, 245)) else (if i.val < 3095 then (141, 73) else (28, 60)))) else (if i.val < 3100 then (if i.val < 3098 then (if i.val < 3097 then (127, 107) else (96, 86)) else (if i.val < 3099 then (15, 242) else (115, 5))) else (if i.val < 3102 then (if i.val < 3101 then (33, 79) else (143, 201)) else (if i.val < 3103 then (136, 199) else (if i.val < 3104 then (115, 44) else (144, 118))))))))) else (if i.val < 3172 then (if i.val < 3138 then (if i.val < 3121 then (if i.val < 3113 then (if i.val < 3109 then (if i.val < 3107 then (if i.val < 3106 then (82, 50) else (121, 204)) else (if i.val < 3108 then (89, 142) else (34, 77))) else (if i.val < 3111 then (if i.val < 3110 then (142, 29) else (56, 95)) else (if i.val < 3112 then (61, 223) else (85, 106)))) else (if i.val < 3117 then (if i.val < 3115 then (if i.val < 3114 then (134, 151) else (123, 30)) else (if i.val < 3116 then (90, 207) else (14, 189))) else (if i.val < 3119 then (if i.val < 3118 then (86, 170) else (84, 138)) else (if i.val < 3120 then (31, 163) else (77, 74))))) else (if i.val < 3129 then (if i.val < 3125 then (if i.val < 3123 then (if i.val < 3122 then (143, 51) else (18, 159)) else (if i.val < 3124 then (62, 2) else (84, 102))) else (if i.val < 3127 then (if i.val < 3126 then (139, 17) else (81, 105)) else (if i.val < 3128 then (116, 96) else (63, 117)))) else (if i.val < 3133 then (if i.val < 3131 then (if i.val < 3130 then (21, 224) else (131, 70)) else (if i.val < 3132 then (16, 24) else (134, 205))) else (if i.val < 3135 then (if i.val < 3134 then (117, 127) else (111, 246)) else (if i.val < 3136 then (75, 34) else (if i.val < 3137 then (67, 106) else (49, 244))))))) else (if i.val < 3155 then (if i.val < 3146 then (if i.val < 3142 then (if i.val < 3140 then (if i.val < 3139 then (140, 108) else (70, 34)) else (if i.val < 3141 then (143, 108) else (122, 184))) else (if i.val < 3144 then (if i.val < 3143 then (121, 148) else (1, 44)) else (if i.val < 3145 then (57, 25) else (41, 156)))) else (if i.val < 3150 then (if i.val < 3148 then (if i.val < 3147 then (2, 204) else (109, 137)) else (if i.val < 3149 then (88, 60) else (83, 123))) else (if i.val < 3152 then (if i.val < 3151 then (87, 245) else (104, 47)) else (if i.val < 3153 then (118, 63) else (if i.val < 3154 then (46, 246) else (130, 182)))))) else (if i.val < 3163 then (if i.val < 3159 then (if i.val < 3157 then (if i.val < 3156 then (131, 234) else (68, 43)) else (if i.val < 3158 then (133, 233) else (83, 37))) else (if i.val < 3161 then (if i.val < 3160 then (119, 4) else (113, 55)) else (if i.val < 3162 then (89, 245) else (130, 75)))) else (if i.val < 3167 then (if i.val < 3165 then (if i.val < 3164 then (143, 53) else (118, 38)) else (if i.val < 3166 then (0, 252) else (141, 228))) else (if i.val < 3169 then (if i.val < 3168 then (82, 239) else (81, 58)) else (if i.val < 3170 then (87, 243) else (if i.val < 3171 then (79, 136) else (31, 126)))))))) else (if i.val < 3206 then (if i.val < 3189 then (if i.val < 3180 then (if i.val < 3176 then (if i.val < 3174 then (if i.val < 3173 then (82, 107) else (38, 125)) else (if i.val < 3175 then (135, 182) else (129, 86))) else (if i.val < 3178 then (if i.val < 3177 then (22, 251) else (18, 58)) else (if i.val < 3179 then (128, 0) else (2, 132)))) else (if i.val < 3184 then (if i.val < 3182 then (if i.val < 3181 then (49, 219) else (53, 206)) else (if i.val < 3183 then (134, 222) else (137, 54))) else (if i.val < 3186 then (if i.val < 3185 then (40, 89) else (138, 6)) else (if i.val < 3187 then (44, 150) else (if i.val < 3188 then (61, 188) else (82, 173)))))) else (if i.val < 3197 then (if i.val < 3193 then (if i.val < 3191 then (if i.val < 3190 then (144, 201) else (111, 76)) else (if i.val < 3192 then (138, 84) else (90, 135))) else (if i.val < 3195 then (if i.val < 3194 then (141, 243) else (121, 51)) else (if i.val < 3196 then (138, 184) else (143, 109)))) else (if i.val < 3201 then (if i.val < 3199 then (if i.val < 3198 then (99, 175) else (139, 160)) else (if i.val < 3200 then (110, 247) else (138, 194))) else (if i.val < 3203 then (if i.val < 3202 then (140, 114) else (142, 156)) else (if i.val < 3204 then (140, 54) else (if i.val < 3205 then (140, 253) else (61, 97))))))) else (if i.val < 3223 then (if i.val < 3214 then (if i.val < 3210 then (if i.val < 3208 then (if i.val < 3207 then (128, 253) else (36, 62)) else (if i.val < 3209 then (144, 77) else (134, 181))) else (if i.val < 3212 then (if i.val < 3211 then (111, 22) else (61, 137)) else (if i.val < 3213 then (135, 204) else (92, 129)))) else (if i.val < 3218 then (if i.val < 3216 then (if i.val < 3215 then (118, 7) else (81, 37)) else (if i.val < 3217 then (121, 32) else (137, 5))) else (if i.val < 3220 then (if i.val < 3219 then (142, 10) else (143, 184)) else (if i.val < 3221 then (141, 41) else (if i.val < 3222 then (122, 40) else (116, 253)))))) else (if i.val < 3231 then (if i.val < 3227 then (if i.val < 3225 then (if i.val < 3224 then (66, 35) else (106, 93)) else (if i.val < 3226 then (20, 13) else (107, 104))) else (if i.val < 3229 then (if i.val < 3228 then (115, 94) else (135, 45)) else (if i.val < 3230 then (68, 24) else (46, 94)))) else (if i.val < 3235 then (if i.val < 3233 then (if i.val < 3232 then (97, 212) else (89, 215)) else (if i.val < 3234 then (39, 5) else (22, 109))) else (if i.val < 3237 then (if i.val < 3236 then (144, 5) else (8, 51)) else (if i.val < 3238 then (32, 238) else (if i.val < 3239 then (138, 101) else (134, 85)))))))))))) else (if i.val < 3780 then (if i.val < 3510 then (if i.val < 3375 then (if i.val < 3307 then (if i.val < 3273 then (if i.val < 3256 then (if i.val < 3248 then (if i.val < 3244 then (if i.val < 3242 then (if i.val < 3241 then (32, 235) else (104, 254)) else (if i.val < 3243 then (64, 99) else (143, 125))) else (if i.val < 3246 then (if i.val < 3245 then (141, 40) else (143, 156)) else (if i.val < 3247 then (27, 140) else (130, 62)))) else (if i.val < 3252 then (if i.val < 3250 then (if i.val < 3249 then (138, 160) else (134, 110)) else (if i.val < 3251 then (86, 182) else (136, 5))) else (if i.val < 3254 then (if i.val < 3253 then (132, 40) else (98, 91)) else (if i.val < 3255 then (141, 186) else (126, 221))))) else (if i.val < 3264 then (if i.val < 3260 then (if i.val < 3258 then (if i.val < 3257 then (82, 93) else (118, 9)) else (if i.val < 3259 then (99, 253) else (137, 108))) else (if i.val < 3262 then (if i.val < 3261 then (140, 93) else (15, 62)) else (if i.val < 3263 then (121, 216) else (86, 129)))) else (if i.val < 3268 then (if i.val < 3266 then (if i.val < 3265 then (114, 41) else (70, 62)) else (if i.val < 3267 then (45, 214) else (142, 49))) else (if i.val < 3270 then (if i.val < 3269 then (138, 157) else (143, 90)) else (if i.val < 3271 then (124, 60) else (if i.val < 3272 then (142, 196) else (144, 190))))))) else (if i.val < 3290 then (if i.val < 3281 then (if i.val < 3277 then (if i.val < 3275 then (if i.val < 3274 then (93, 250) else (82, 138)) else (if i.val < 3276 then (87, 175) else (25, 24))) else (if i.val < 3279 then (if i.val < 3278 then (56, 249) else (84, 21)) else (if i.val < 3280 then (67, 68) else (95, 127)))) else (if i.val < 3285 then (if i.val < 3283 then (if i.val < 3282 then (137, 254) else (139, 217)) else (if i.val < 3284 then (69, 99) else (38, 46))) else (if i.val < 3287 then (if i.val < 3286 then (92, 223) else (89, 158)) else (if i.val < 3288 then (57, 61) else (if i.val < 3289 then (132, 11) else (107, 119)))))) else (if i.val < 3298 then (if i.val < 3294 then (if i.val < 3292 then (if i.val < 3291 then (138, 118) else (115, 31)) else (if i.val < 3293 then (97, 54) else (54, 101))) else (if i.val < 3296 then (if i.val < 3295 then (42, 99) else (90, 10)) else (if i.val < 3297 then (144, 76) else (132, 199)))) else (if i.val < 3302 then (if i.val < 3300 then (if i.val < 3299 then (144, 32) else (79, 0)) else (if i.val < 3301 then (136, 83) else (89, 204))) else (if i.val < 3304 then (if i.val < 3303 then (94, 109) else (134, 231)) else (if i.val < 3305 then (84, 92) else (if i.val < 3306 then (131, 66) else (80, 28)))))))) else (if i.val < 3341 then (if i.val < 3324 then (if i.val < 3315 then (if i.val < 3311 then (if i.val < 3309 then (if i.val < 3308 then (70, 128) else (61, 55)) else (if i.val < 3310 then (133, 126) else (87, 149))) else (if i.val < 3313 then (if i.val < 3312 then (110, 76) else (67, 58)) else (if i.val < 3314 then (142, 26) else (143, 170)))) else (if i.val < 3319 then (if i.val < 3317 then (if i.val < 3316 then (93, 242) else (105, 56)) else (if i.val < 3318 then (122, 109) else (128, 89))) else (if i.val < 3321 then (if i.val < 3320 then (74, 68) else (51, 203)) else (if i.val < 3322 then (42, 106) else (if i.val < 3323 then (45, 133) else (73, 184)))))) else (if i.val < 3332 then (if i.val < 3328 then (if i.val < 3326 then (if i.val < 3325 then (64, 23) else (140, 221)) else (if i.val < 3327 then (130, 58) else (34, 237))) else (if i.val < 3330 then (if i.val < 3329 then (112, 228) else (69, 215)) else (if i.val < 3331 then (87, 151) else (104, 38)))) else (if i.val < 3336 then (if i.val < 3334 then (if i.val < 3333 then (52, 179) else (113, 195)) else (if i.val < 3335 then (129, 129) else (71, 91))) else (if i.val < 3338 then (if i.val < 3337 then (61, 27) else (142, 162)) else (if i.val < 3339 then (29, 61) else (if i.val < 3340 then (132, 172) else (134, 69))))))) else (if i.val < 3358 then (if i.val < 3349 then (if i.val < 3345 then (if i.val < 3343 then (if i.val < 3342 then (110, 25) else (136, 121)) else (if i.val < 3344 then (46, 163) else (139, 150))) else (if i.val < 3347 then (if i.val < 3346 then (135, 16) else (140, 212)) else (if i.val < 3348 then (136, 160) else (116, 50)))) else (if i.val < 3353 then (if i.val < 3351 then (if i.val < 3350 then (9, 156) else (54, 222)) else (if i.val < 3352 then (66, 214) else (93, 228))) else (if i.val < 3355 then (if i.val < 3354 then (123, 213) else (122, 15)) else (if i.val < 3356 then (142, 79) else (if i.val < 3357 then (75, 228) else (96, 55)))))) else (if i.val < 3366 then (if i.val < 3362 then (if i.val < 3360 then (if i.val < 3359 then (30, 70) else (98, 217)) else (if i.val < 3361 then (80, 190) else (122, 130))) else (if i.val < 3364 then (if i.val < 3363 then (31, 160) else (119, 211)) else (if i.val < 3365 then (95, 48) else (88, 137)))) else (if i.val < 3370 then (if i.val < 3368 then (if i.val < 3367 then (17, 160) else (143, 153)) else (if i.val < 3369 then (100, 187) else (139, 176))) else (if i.val < 3372 then (if i.val < 3371 then (57, 229) else (130, 140)) else (if i.val < 3373 then (49, 116) else (if i.val < 3374 then (112, 164) else (106, 78))))))))) else (if i.val < 3442 then (if i.val < 3408 then (if i.val < 3391 then (if i.val < 3383 then (if i.val < 3379 then (if i.val < 3377 then (if i.val < 3376 then (97, 205) else (134, 67)) else (if i.val < 3378 then (9, 243) else (48, 24))) else (if i.val < 3381 then (if i.val < 3380 then (142, 88) else (134, 135)) else (if i.val < 3382 then (129, 47) else (124, 190)))) else (if i.val < 3387 then (if i.val < 3385 then (if i.val < 3384 then (137, 99) else (20, 183)) else (if i.val < 3386 then (118, 230) else (100, 165))) else (if i.val < 3389 then (if i.val < 3388 then (128, 123) else (91, 43)) else (if i.val < 3390 then (115, 136) else (136, 53))))) else (if i.val < 3399 then (if i.val < 3395 then (if i.val < 3393 then (if i.val < 3392 then (98, 1) else (37, 234)) else (if i.val < 3394 then (135, 192) else (124, 63))) else (if i.val < 3397 then (if i.val < 3396 then (144, 1) else (85, 204)) else (if i.val < 3398 then (15, 255) else (47, 140)))) else (if i.val < 3403 then (if i.val < 3401 then (if i.val < 3400 then (127, 59) else (49, 142)) else (if i.val < 3402 then (130, 116) else (21, 43))) else (if i.val < 3405 then (if i.val < 3404 then (131, 64) else (72, 212)) else (if i.val < 3406 then (112, 157) else (if i.val < 3407 then (142, 25) else (129, 57))))))) else (if i.val < 3425 then (if i.val < 3416 then (if i.val < 3412 then (if i.val < 3410 then (if i.val < 3409 then (82, 188) else (52, 222)) else (if i.val < 3411 then (143, 214) else (131, 212))) else (if i.val < 3414 then (if i.val < 3413 then (102, 192) else (124, 31)) else (if i.val < 3415 then (117, 55) else (97, 45)))) else (if i.val < 3420 then (if i.val < 3418 then (if i.val < 3417 then (124, 108) else (141, 111)) else (if i.val < 3419 then (25, 63) else (97, 200))) else (if i.val < 3422 then (if i.val < 3421 then (98, 240) else (143, 171)) else (if i.val < 3423 then (129, 168) else (if i.val < 3424 then (130, 9) else (124, 212)))))) else (if i.val < 3433 then (if i.val < 3429 then (if i.val < 3427 then (if i.val < 3426 then (74, 141) else (78, 224)) else (if i.val < 3428 then (111, 57) else (129, 228))) else (if i.val < 3431 then (if i.val < 3430 then (2, 227) else (57, 118)) else (if i.val < 3432 then (117, 144) else (116, 215)))) else (if i.val < 3437 then (if i.val < 3435 then (if i.val < 3434 then (110, 253) else (111, 3)) else (if i.val < 3436 then (138, 209) else (95, 160))) else (if i.val < 3439 then (if i.val < 3438 then (101, 155) else (111, 166)) else (if i.val < 3440 then (38, 130) else (if i.val < 3441 then (137, 125) else (57, 169)))))))) else (if i.val < 3476 then (if i.val < 3459 then (if i.val < 3450 then (if i.val < 3446 then (if i.val < 3444 then (if i.val < 3443 then (132, 130) else (139, 92)) else (if i.val < 3445 then (89, 159) else (68, 156))) else (if i.val < 3448 then (if i.val < 3447 then (99, 237) else (132, 216)) else (if i.val < 3449 then (58, 170) else (144, 222)))) else (if i.val < 3454 then (if i.val < 3452 then (if i.val < 3451 then (79, 60) else (43, 44)) else (if i.val < 3453 then (44, 120) else (131, 131))) else (if i.val < 3456 then (if i.val < 3455 then (78, 12) else (72, 251)) else (if i.val < 3457 then (125, 18) else (if i.val < 3458 then (108, 231) else (52, 46)))))) else (if i.val < 3467 then (if i.val < 3463 then (if i.val < 3461 then (if i.val < 3460 then (67, 239) else (8, 45)) else (if i.val < 3462 then (44, 250) else (88, 110))) else (if i.val < 3465 then (if i.val < 3464 then (104, 158) else (39, 144)) else (if i.val < 3466 then (54, 125) else (122, 178)))) else (if i.val < 3471 then (if i.val < 3469 then (if i.val < 3468 then (144, 150) else (6, 44)) else (if i.val < 3470 then (99, 76) else (88, 50))) else (if i.val < 3473 then (if i.val < 3472 then (86, 77) else (125, 236)) else (if i.val < 3474 then (144, 182) else (if i.val < 3475 then (143, 42) else (85, 62))))))) else (if i.val < 3493 then (if i.val < 3484 then (if i.val < 3480 then (if i.val < 3478 then (if i.val < 3477 then (139, 108) else (137, 118)) else (if i.val < 3479 then (106, 179) else (52, 78))) else (if i.val < 3482 then (if i.val < 3481 then (143, 11) else (70, 15)) else (if i.val < 3483 then (75, 16) else (89, 49)))) else (if i.val < 3488 then (if i.val < 3486 then (if i.val < 3485 then (53, 203) else (125, 89)) else (if i.val < 3487 then (121, 100) else (49, 41))) else (if i.val < 3490 then (if i.val < 3489 then (85, 102) else (109, 230)) else (if i.val < 3491 then (63, 178) else (if i.val < 3492 then (102, 205) else (103, 216)))))) else (if i.val < 3501 then (if i.val < 3497 then (if i.val < 3495 then (if i.val < 3494 then (123, 92) else (144, 21)) else (if i.val < 3496 then (134, 255) else (121, 245))) else (if i.val < 3499 then (if i.val < 3498 then (116, 183) else (144, 41)) else (if i.val < 3500 then (17, 110) else (85, 25)))) else (if i.val < 3505 then (if i.val < 3503 then (if i.val < 3502 then (121, 131) else (128, 118)) else (if i.val < 3504 then (4, 121) else (132, 31))) else (if i.val < 3507 then (if i.val < 3506 then (113, 59) else (19, 166)) else (if i.val < 3508 then (73, 254) else (if i.val < 3509 then (109, 205) else (11, 81)))))))))) else (if i.val < 3645 then (if i.val < 3577 then (if i.val < 3543 then (if i.val < 3526 then (if i.val < 3518 then (if i.val < 3514 then (if i.val < 3512 then (if i.val < 3511 then (70, 180) else (1, 120)) else (if i.val < 3513 then (135, 103) else (143, 252))) else (if i.val < 3516 then (if i.val < 3515 then (46, 198) else (137, 97)) else (if i.val < 3517 then (76, 159) else (35, 105)))) else (if i.val < 3522 then (if i.val < 3520 then (if i.val < 3519 then (133, 70) else (42, 135)) else (if i.val < 3521 then (137, 255) else (86, 133))) else (if i.val < 3524 then (if i.val < 3523 then (94, 209) else (84, 243)) else (if i.val < 3525 then (40, 184) else (16, 48))))) else (if i.val < 3534 then (if i.val < 3530 then (if i.val < 3528 then (if i.val < 3527 then (138, 159) else (102, 75)) else (if i.val < 3529 then (141, 163) else (105, 194))) else (if i.val < 3532 then (if i.val < 3531 then (48, 141) else (133, 74)) else (if i.val < 3533 then (134, 87) else (104, 67)))) else (if i.val < 3538 then (if i.val < 3536 then (if i.val < 3535 then (136, 45) else (102, 1)) else (if i.val < 3537 then (93, 102) else (143, 161))) else (if i.val < 3540 then (if i.val < 3539 then (142, 42) else (130, 142)) else (if i.val < 3541 then (50, 192) else (if i.val < 3542 then (81, 202) else (132, 177))))))) else (if i.val < 3560 then (if i.val < 3551 then (if i.val < 3547 then (if i.val < 3545 then (if i.val < 3544 then (87, 186) else (106, 62)) else (if i.val < 3546 then (84, 195) else (116, 45))) else (if i.val < 3549 then (if i.val < 3548 then (70, 92) else (77, 178)) else (if i.val < 3550 then (101, 163) else (133, 15)))) else (if i.val < 3555 then (if i.val < 3553 then (if i.val < 3552 then (102, 141) else (2, 153)) else (if i.val < 3554 then (104, 48) else (53, 73))) else (if i.val < 3557 then (if i.val < 3556 then (114, 135) else (139, 184)) else (if i.val < 3558 then (128, 14) else (if i.val < 3559 then (125, 122) else (134, 224)))))) else (if i.val < 3568 then (if i.val < 3564 then (if i.val < 3562 then (if i.val < 3561 then (116, 206) else (133, 148)) else (if i.val < 3563 then (41, 204) else (114, 12))) else (if i.val < 3566 then (if i.val < 3565 then (141, 178) else (63, 83)) else (if i.val < 3567 then (45, 139) else (134, 156)))) else (if i.val < 3572 then (if i.val < 3570 then (if i.val < 3569 then (69, 226) else (80, 75)) else (if i.val < 3571 then (139, 237) else (86, 28))) else (if i.val < 3574 then (if i.val < 3573 then (97, 167) else (56, 181)) else (if i.val < 3575 then (84, 13) else (if i.val < 3576 then (79, 85) else (135, 236)))))))) else (if i.val < 3611 then (if i.val < 3594 then (if i.val < 3585 then (if i.val < 3581 then (if i.val < 3579 then (if i.val < 3578 then (131, 158) else (132, 179)) else (if i.val < 3580 then (88, 249) else (137, 141))) else (if i.val < 3583 then (if i.val < 3582 then (122, 11) else (127, 45)) else (if i.val < 3584 then (59, 152) else (55, 188)))) else (if i.val < 3589 then (if i.val < 3587 then (if i.val < 3586 then (69, 97) else (143, 254)) else (if i.val < 3588 then (70, 161) else (88, 221))) else (if i.val < 3591 then (if i.val < 3590 then (132, 185) else (101, 44)) else (if i.val < 3592 then (111, 243) else (if i.val < 3593 then (49, 103) else (127, 14)))))) else (if i.val < 3602 then (if i.val < 3598 then (if i.val < 3596 then (if i.val < 3595 then (87, 144) else (142, 193)) else (if i.val < 3597 then (132, 120) else (126, 69))) else (if i.val < 3600 then (if i.val < 3599 then (13, 159) else (10, 102)) else (if i.val < 3601 then (74, 196) else (111, 84)))) else (if i.val < 3606 then (if i.val < 3604 then (if i.val < 3603 then (134, 82) else (123, 215)) else (if i.val < 3605 then (117, 188) else (83, 254))) else (if i.val < 3608 then (if i.val < 3607 then (90, 170) else (142, 219)) else (if i.val < 3609 then (68, 63) else (if i.val < 3610 then (86, 43) else (102, 66))))))) else (if i.val < 3628 then (if i.val < 3619 then (if i.val < 3615 then (if i.val < 3613 then (if i.val < 3612 then (78, 194) else (49, 95)) else (if i.val < 3614 then (86, 82) else (29, 121))) else (if i.val < 3617 then (if i.val < 3616 then (117, 159) else (66, 89)) else (if i.val < 3618 then (98, 28) else (69, 189)))) else (if i.val < 3623 then (if i.val < 3621 then (if i.val < 3620 then (55, 139) else (141, 144)) else (if i.val < 3622 then (90, 76) else (143, 93))) else (if i.val < 3625 then (if i.val < 3624 then (110, 165) else (76, 253)) else (if i.val < 3626 then (68, 174) else (if i.val < 3627 then (132, 164) else (74, 124)))))) else (if i.val < 3636 then (if i.val < 3632 then (if i.val < 3630 then (if i.val < 3629 then (39, 25) else (73, 97)) else (if i.val < 3631 then (91, 96) else (47, 32))) else (if i.val < 3634 then (if i.val < 3633 then (27, 199) else (137, 98)) else (if i.val < 3635 then (33, 220) else (132, 147)))) else (if i.val < 3640 then (if i.val < 3638 then (if i.val < 3637 then (3, 196) else (34, 109)) else (if i.val < 3639 then (135, 249) else (127, 92))) else (if i.val < 3642 then (if i.val < 3641 then (117, 103) else (13, 101)) else (if i.val < 3643 then (142, 34) else (if i.val < 3644 then (132, 53) else (62, 195))))))))) else (if i.val < 3712 then (if i.val < 3678 then (if i.val < 3661 then (if i.val < 3653 then (if i.val < 3649 then (if i.val < 3647 then (if i.val < 3646 then (137, 113) else (11, 237)) else (if i.val < 3648 then (59, 184) else (70, 22))) else (if i.val < 3651 then (if i.val < 3650 then (26, 129) else (133, 0)) else (if i.val < 3652 then (114, 198) else (144, 136)))) else (if i.val < 3657 then (if i.val < 3655 then (if i.val < 3654 then (85, 80) else (112, 106)) else (if i.val < 3656 then (59, 30) else (84, 32))) else (if i.val < 3659 then (if i.val < 3658 then (4, 31) else (131, 40)) else (if i.val < 3660 then (131, 188) else (128, 232))))) else (if i.val < 3669 then (if i.val < 3665 then (if i.val < 3663 then (if i.val < 3662 then (105, 156) else (69, 44)) else (if i.val < 3664 then (112, 253) else (88, 250))) else (if i.val < 3667 then (if i.val < 3666 then (114, 186) else (72, 72)) else (if i.val < 3668 then (142, 169) else (126, 236)))) else (if i.val < 3673 then (if i.val < 3671 then (if i.val < 3670 then (113, 196) else (105, 149)) else (if i.val < 3672 then (115, 72) else (21, 198))) else (if i.val < 3675 then (if i.val < 3674 then (109, 89) else (21, 214)) else (if i.val < 3676 then (71, 18) else (if i.val < 3677 then (138, 250) else (37, 67))))))) else (if i.val < 3695 then (if i.val < 3686 then (if i.val < 3682 then (if i.val < 3680 then (if i.val < 3679 then (9, 248) else (135, 3)) else (if i.val < 3681 then (121, 14) else (127, 255))) else (if i.val < 3684 then (if i.val < 3683 then (131, 52) else (131, 202)) else (if i.val < 3685 then (112, 177) else (113, 105)))) else (if i.val < 3690 then (if i.val < 3688 then (if i.val < 3687 then (88, 134) else (117, 10)) else (if i.val < 3689 then (61, 44) else (112, 160))) else (if i.val < 3692 then (if i.val < 3691 then (113, 182) else (125, 61)) else (if i.val < 3693 then (94, 151) else (if i.val < 3694 then (97, 76) else (121, 248)))))) else (if i.val < 3703 then (if i.val < 3699 then (if i.val < 3697 then (if i.val < 3696 then (135, 208) else (115, 120)) else (if i.val < 3698 then (66, 200) else (101, 221))) else (if i.val < 3701 then (if i.val < 3700 then (113, 7) else (144, 113)) else (if i.val < 3702 then (90, 66) else (134, 147)))) else (if i.val < 3707 then (if i.val < 3705 then (if i.val < 3704 then (68, 59) else (126, 40)) else (if i.val < 3706 then (81, 49) else (105, 142))) else (if i.val < 3709 then (if i.val < 3708 then (105, 148) else (40, 67)) else (if i.val < 3710 then (62, 20) else (if i.val < 3711 then (24, 204) else (126, 237)))))))) else (if i.val < 3746 then (if i.val < 3729 then (if i.val < 3720 then (if i.val < 3716 then (if i.val < 3714 then (if i.val < 3713 then (87, 196) else (69, 252)) else (if i.val < 3715 then (102, 166) else (105, 214))) else (if i.val < 3718 then (if i.val < 3717 then (28, 138) else (37, 81)) else (if i.val < 3719 then (143, 47) else (116, 148)))) else (if i.val < 3724 then (if i.val < 3722 then (if i.val < 3721 then (141, 127) else (79, 62)) else (if i.val < 3723 then (67, 215) else (138, 54))) else (if i.val < 3726 then (if i.val < 3725 then (141, 102) else (142, 182)) else (if i.val < 3727 then (102, 164) else (if i.val < 3728 then (105, 34) else (132, 92)))))) else (if i.val < 3737 then (if i.val < 3733 then (if i.val < 3731 then (if i.val < 3730 then (20, 194) else (88, 54)) else (if i.val < 3732 then (33, 185) else (128, 64))) else (if i.val < 3735 then (if i.val < 3734 then (132, 254) else (140, 12)) else (if i.val < 3736 then (137, 126) else (123, 186)))) else (if i.val < 3741 then (if i.val < 3739 then (if i.val < 3738 then (140, 231) else (133, 186)) else (if i.val < 3740 then (135, 92) else (120, 15))) else (if i.val < 3743 then (if i.val < 3742 then (139, 135) else (86, 17)) else (if i.val < 3744 then (104, 21) else (if i.val < 3745 then (82, 94) else (81, 188))))))) else (if i.val < 3763 then (if i.val < 3754 then (if i.val < 3750 then (if i.val < 3748 then (if i.val < 3747 then (80, 150) else (42, 35)) else (if i.val < 3749 then (96, 222) else (50, 26))) else (if i.val < 3752 then (if i.val < 3751 then (10, 132) else (140, 179)) else (if i.val < 3753 then (5, 78) else (130, 8)))) else (if i.val < 3758 then (if i.val < 3756 then (if i.val < 3755 then (143, 2) else (32, 88)) else (if i.val < 3757 then (17, 189) else (143, 166))) else (if i.val < 3760 then (if i.val < 3759 then (113, 61) else (32, 174)) else (if i.val < 3761 then (21, 188) else (if i.val < 3762 then (4, 97) else (49, 113)))))) else (if i.val < 3771 then (if i.val < 3767 then (if i.val < 3765 then (if i.val < 3764 then (84, 180) else (22, 112)) else (if i.val < 3766 then (4, 70) else (129, 73))) else (if i.val < 3769 then (if i.val < 3768 then (70, 143) else (28, 111)) else (if i.val < 3770 then (21, 46) else (104, 69)))) else (if i.val < 3775 then (if i.val < 3773 then (if i.val < 3772 then (88, 107) else (85, 27)) else (if i.val < 3774 then (134, 148) else (133, 246))) else (if i.val < 3777 then (if i.val < 3776 then (96, 24) else (85, 84)) else (if i.val < 3778 then (141, 219) else (if i.val < 3779 then (70, 26) else (143, 12))))))))))) else (if i.val < 4050 then (if i.val < 3915 then (if i.val < 3847 then (if i.val < 3813 then (if i.val < 3796 then (if i.val < 3788 then (if i.val < 3784 then (if i.val < 3782 then (if i.val < 3781 then (144, 104) else (33, 52)) else (if i.val < 3783 then (136, 236) else (137, 150))) else (if i.val < 3786 then (if i.val < 3785 then (124, 224) else (138, 117)) else (if i.val < 3787 then (100, 139) else (115, 141)))) else (if i.val < 3792 then (if i.val < 3790 then (if i.val < 3789 then (30, 120) else (94, 31)) else (if i.val < 3791 then (79, 181) else (96, 88))) else (if i.val < 3794 then (if i.val < 3793 then (143, 54) else (25, 100)) else (if i.val < 3795 then (9, 215) else (92, 179))))) else (if i.val < 3804 then (if i.val < 3800 then (if i.val < 3798 then (if i.val < 3797 then (133, 27) else (67, 54)) else (if i.val < 3799 then (40, 190) else (4, 99))) else (if i.val < 3802 then (if i.val < 3801 then (105, 126) else (5, 116)) else (if i.val < 3803 then (143, 175) else (119, 149)))) else (if i.val < 3808 then (if i.val < 3806 then (if i.val < 3805 then (138, 3) else (141, 116)) else (if i.val < 3807 then (56, 247) else (134, 127))) else (if i.val < 3810 then (if i.val < 3809 then (25, 116) else (139, 255)) else (if i.val < 3811 then (11, 141) else (if i.val < 3812 then (141, 191) else (95, 26))))))) else (if i.val < 3830 then (if i.val < 3821 then (if i.val < 3817 then (if i.val < 3815 then (if i.val < 3814 then (133, 24) else (120, 189)) else (if i.val < 3816 then (41, 119) else (109, 117))) else (if i.val < 3819 then (if i.val < 3818 then (133, 135) else (130, 120)) else (if i.val < 3820 then (142, 238) else (32, 70)))) else (if i.val < 3825 then (if i.val < 3823 then (if i.val < 3822 then (30, 184) else (117, 194)) else (if i.val < 3824 then (4, 145) else (140, 175))) else (if i.val < 3827 then (if i.val < 3826 then (136, 73) else (16, 195)) else (if i.val < 3828 then (111, 222) else (if i.val < 3829 then (142, 240) else (125, 9)))))) else (if i.val < 3838 then (if i.val < 3834 then (if i.val < 3832 then (if i.val < 3831 then (130, 42) else (95, 5)) else (if i.val < 3833 then (95, 240) else (122, 5))) else (if i.val < 3836 then (if i.val < 3835 then (142, 159) else (129, 18)) else (if i.val < 3837 then (142, 96) else (137, 43)))) else (if i.val < 3842 then (if i.val < 3840 then (if i.val < 3839 then (119, 147) else (128, 63)) else (if i.val < 3841 then (144, 57) else (117, 229))) else (if i.val < 3844 then (if i.val < 3843 then (86, 163) else (73, 51)) else (if i.val < 3845 then (29, 68) else (if i.val < 3846 then (73, 27) else (117, 87)))))))) else (if i.val < 3881 then (if i.val < 3864 then (if i.val < 3855 then (if i.val < 3851 then (if i.val < 3849 then (if i.val < 3848 then (139, 188) else (64, 140)) else (if i.val < 3850 then (135, 148) else (25, 29))) else (if i.val < 3853 then (if i.val < 3852 then (65, 69) else (55, 162)) else (if i.val < 3854 then (56, 129) else (58, 167)))) else (if i.val < 3859 then (if i.val < 3857 then (if i.val < 3856 then (23, 112) else (97, 119)) else (if i.val < 3858 then (138, 145) else (92, 210))) else (if i.val < 3861 then (if i.val < 3860 then (25, 152) else (122, 80)) else (if i.val < 3862 then (107, 207) else (if i.val < 3863 then (135, 190) else (130, 118)))))) else (if i.val < 3872 then (if i.val < 3868 then (if i.val < 3866 then (if i.val < 3865 then (55, 225) else (68, 42)) else (if i.val < 3867 then (3, 183) else (120, 37))) else (if i.val < 3870 then (if i.val < 3869 then (124, 112) else (131, 214)) else (if i.val < 3871 then (41, 25) else (118, 35)))) else (if i.val < 3876 then (if i.val < 3874 then (if i.val < 3873 then (12, 120) else (118, 210)) else (if i.val < 3875 then (36, 239) else (62, 193))) else (if i.val < 3878 then (if i.val < 3877 then (138, 227) else (12, 128)) else (if i.val < 3879 then (133, 213) else (if i.val < 3880 then (110, 114) else (143, 173))))))) else (if i.val < 3898 then (if i.val < 3889 then (if i.val < 3885 then (if i.val < 3883 then (if i.val < 3882 then (57, 245) else (123, 2)) else (if i.val < 3884 then (4, 193) else (102, 195))) else (if i.val < 3887 then (if i.val < 3886 then (119, 33) else (99, 61)) else (if i.val < 3888 then (36, 37) else (131, 179)))) else (if i.val < 3893 then (if i.val < 3891 then (if i.val < 3890 then (100, 177) else (10, 213)) else (if i.val < 3892 then (96, 23) else (135, 5))) else (if i.val < 3895 then (if i.val < 3894 then (72, 34) else (124, 11)) else (if i.val < 3896 then (75, 227) else (if i.val < 3897 then (142, 249) else (98, 102)))))) else (if i.val < 3906 then (if i.val < 3902 then (if i.val < 3900 then (if i.val < 3899 then (134, 25) else (80, 74)) else (if i.val < 3901 then (12, 41) else (53, 115))) else (if i.val < 3904 then (if i.val < 3903 then (142, 232) else (115, 233)) else (if i.val < 3905 then (14, 45) else (85, 125)))) else (if i.val < 3910 then (if i.val < 3908 then (if i.val < 3907 then (88, 38) else (107, 7)) else (if i.val < 3909 then (135, 87) else (144, 148))) else (if i.val < 3912 then (if i.val < 3911 then (131, 90) else (75, 255)) else (if i.val < 3913 then (122, 51) else (if i.val < 3914 then (118, 234) else (12, 46))))))))) else (if i.val < 3982 then (if i.val < 3948 then (if i.val < 3931 then (if i.val < 3923 then (if i.val < 3919 then (if i.val < 3917 then (if i.val < 3916 then (126, 170) else (109, 111)) else (if i.val < 3918 then (144, 208) else (73, 20))) else (if i.val < 3921 then (if i.val < 3920 then (131, 6) else (80, 187)) else (if i.val < 3922 then (54, 217) else (99, 144)))) else (if i.val < 3927 then (if i.val < 3925 then (if i.val < 3924 then (141, 238) else (94, 87)) else (if i.val < 3926 then (123, 209) else (102, 152))) else (if i.val < 3929 then (if i.val < 3928 then (115, 251) else (122, 74)) else (if i.val < 3930 then (23, 159) else (121, 252))))) else (if i.val < 3939 then (if i.val < 3935 then (if i.val < 3933 then (if i.val < 3932 then (143, 233) else (137, 147)) else (if i.val < 3934 then (71, 113) else (25, 207))) else (if i.val < 3937 then (if i.val < 3936 then (11, 191) else (124, 32)) else (if i.val < 3938 then (34, 122) else (111, 140)))) else (if i.val < 3943 then (if i.val < 3941 then (if i.val < 3940 then (98, 98) else (133, 204)) else (if i.val < 3942 then (118, 129) else (131, 173))) else (if i.val < 3945 then (if i.val < 3944 then (142, 198) else (14, 38)) else (if i.val < 3946 then (87, 226) else (if i.val < 3947 then (85, 59) else (67, 222))))))) else (if i.val < 3965 then (if i.val < 3956 then (if i.val < 3952 then (if i.val < 3950 then (if i.val < 3949 then (102, 111) else (121, 143)) else (if i.val < 3951 then (115, 184) else (62, 74))) else (if i.val < 3954 then (if i.val < 3953 then (1, 98) else (102, 120)) else (if i.val < 3955 then (53, 241) else (112, 178)))) else (if i.val < 3960 then (if i.val < 3958 then (if i.val < 3957 then (137, 21) else (110, 185)) else (if i.val < 3959 then (124, 141) else (107, 2))) else (if i.val < 3962 then (if i.val < 3961 then (134, 114) else (9, 1)) else (if i.val < 3963 then (18, 154) else (if i.val < 3964 then (11, 228) else (137, 45)))))) else (if i.val < 3973 then (if i.val < 3969 then (if i.val < 3967 then (if i.val < 3966 then (63, 195) else (47, 254)) else (if i.val < 3968 then (55, 4) else (131, 157))) else (if i.val < 3971 then (if i.val < 3970 then (96, 57) else (85, 9)) else (if i.val < 3972 then (73, 95) else (65, 193)))) else (if i.val < 3977 then (if i.val < 3975 then (if i.val < 3974 then (143, 187) else (122, 138)) else (if i.val < 3976 then (93, 93) else (5, 250))) else (if i.val < 3979 then (if i.val < 3978 then (135, 216) else (141, 187)) else (if i.val < 3980 then (92, 184) else (if i.val < 3981 then (53, 126) else (119, 124)))))))) else (if i.val < 4016 then (if i.val < 3999 then (if i.val < 3990 then (if i.val < 3986 then (if i.val < 3984 then (if i.val < 3983 then (139, 73) else (102, 154)) else (if i.val < 3985 then (139, 46) else (16, 143))) else (if i.val < 3988 then (if i.val < 3987 then (1, 111) else (46, 216)) else (if i.val < 3989 then (47, 51) else (120, 254)))) else (if i.val < 3994 then (if i.val < 3992 then (if i.val < 3991 then (126, 240) else (132, 165)) else (if i.val < 3993 then (44, 74) else (78, 9))) else (if i.val < 3996 then (if i.val < 3995 then (132, 155) else (104, 8)) else (if i.val < 3997 then (69, 200) else (if i.val < 3998 then (2, 103) else (97, 193)))))) else (if i.val < 4007 then (if i.val < 4003 then (if i.val < 4001 then (if i.val < 4000 then (121, 175) else (63, 69)) else (if i.val < 4002 then (80, 147) else (60, 11))) else (if i.val < 4005 then (if i.val < 4004 then (131, 125) else (56, 147)) else (if i.val < 4006 then (59, 222) else (142, 224)))) else (if i.val < 4011 then (if i.val < 4009 then (if i.val < 4008 then (129, 55) else (121, 147)) else (if i.val < 4010 then (56, 225) else (53, 7))) else (if i.val < 4013 then (if i.val < 4012 then (25, 236) else (138, 163)) else (if i.val < 4014 then (96, 39) else (if i.val < 4015 then (64, 107) else (135, 197))))))) else (if i.val < 4033 then (if i.val < 4024 then (if i.val < 4020 then (if i.val < 4018 then (if i.val < 4017 then (122, 157) else (32, 64)) else (if i.val < 4019 then (65, 24) else (142, 97))) else (if i.val < 4022 then (if i.val < 4021 then (4, 136) else (137, 76)) else (if i.val < 4023 then (47, 125) else (60, 136)))) else (if i.val < 4028 then (if i.val < 4026 then (if i.val < 4025 then (97, 237) else (122, 68)) else (if i.val < 4027 then (1, 138) else (18, 17))) else (if i.val < 4030 then (if i.val < 4029 then (55, 135) else (100, 240)) else (if i.val < 4031 then (116, 168) else (if i.val < 4032 then (127, 1) else (100, 173)))))) else (if i.val < 4041 then (if i.val < 4037 then (if i.val < 4035 then (if i.val < 4034 then (4, 131) else (14, 118)) else (if i.val < 4036 then (84, 171) else (73, 92))) else (if i.val < 4039 then (if i.val < 4038 then (40, 80) else (144, 221)) else (if i.val < 4040 then (83, 130) else (65, 242)))) else (if i.val < 4045 then (if i.val < 4043 then (if i.val < 4042 then (53, 112) else (127, 126)) else (if i.val < 4044 then (144, 37) else (48, 116))) else (if i.val < 4047 then (if i.val < 4046 then (11, 156) else (19, 179)) else (if i.val < 4048 then (120, 6) else (if i.val < 4049 then (25, 89) else (112, 15)))))))))) else (if i.val < 4185 then (if i.val < 4117 then (if i.val < 4083 then (if i.val < 4066 then (if i.val < 4058 then (if i.val < 4054 then (if i.val < 4052 then (if i.val < 4051 then (44, 147) else (48, 148)) else (if i.val < 4053 then (93, 147) else (106, 173))) else (if i.val < 4056 then (if i.val < 4055 then (99, 65) else (113, 62)) else (if i.val < 4057 then (65, 214) else (133, 161)))) else (if i.val < 4062 then (if i.val < 4060 then (if i.val < 4059 then (54, 194) else (16, 25)) else (if i.val < 4061 then (126, 225) else (17, 248))) else (if i.val < 4064 then (if i.val < 4063 then (72, 15) else (125, 99)) else (if i.val < 4065 then (132, 123) else (143, 116))))) else (if i.val < 4074 then (if i.val < 4070 then (if i.val < 4068 then (if i.val < 4067 then (85, 152) else (98, 223)) else (if i.val < 4069 then (127, 135) else (110, 148))) else (if i.val < 4072 then (if i.val < 4071 then (37, 98) else (101, 37)) else (if i.val < 4073 then (141, 61) else (130, 73)))) else (if i.val < 4078 then (if i.val < 4076 then (if i.val < 4075 then (108, 174) else (45, 126)) else (if i.val < 4077 then (13, 128) else (140, 83))) else (if i.val < 4080 then (if i.val < 4079 then (80, 11) else (132, 25)) else (if i.val < 4081 then (78, 45) else (if i.val < 4082 then (136, 255) else (128, 185))))))) else (if i.val < 4100 then (if i.val < 4091 then (if i.val < 4087 then (if i.val < 4085 then (if i.val < 4084 then (108, 19) else (62, 222)) else (if i.val < 4086 then (38, 10) else (123, 172))) else (if i.val < 4089 then (if i.val < 4088 then (80, 142) else (7, 17)) else (if i.val < 4090 then (122, 27) else (4, 191)))) else (if i.val < 4095 then (if i.val < 4093 then (if i.val < 4092 then (60, 183) else (122, 124)) else (if i.val < 4094 then (118, 238) else (26, 20))) else (if i.val < 4097 then (if i.val < 4096 then (71, 90) else (58, 67)) else (if i.val < 4098 then (74, 174) else (if i.val < 4099 then (6, 227) else (68, 112)))))) else (if i.val < 4108 then (if i.val < 4104 then (if i.val < 4102 then (if i.val < 4101 then (123, 156) else (127, 57)) else (if i.val < 4103 then (45, 48) else (91, 205))) else (if i.val < 4106 then (if i.val < 4105 then (112, 174) else (123, 93)) else (if i.val < 4107 then (139, 68) else (11, 213)))) else (if i.val < 4112 then (if i.val < 4110 then (if i.val < 4109 then (126, 50) else (127, 199)) else (if i.val < 4111 then (128, 200) else (112, 33))) else (if i.val < 4114 then (if i.val < 4113 then (15, 117) else (89, 82)) else (if i.val < 4115 then (131, 176) else (if i.val < 4116 then (135, 33) else (77, 105)))))))) else (if i.val < 4151 then (if i.val < 4134 then (if i.val < 4125 then (if i.val < 4121 then (if i.val < 4119 then (if i.val < 4118 then (106, 187) else (129, 231)) else (if i.val < 4120 then (115, 202) else (56, 201))) else (if i.val < 4123 then (if i.val < 4122 then (68, 175) else (139, 107)) else (if i.val < 4124 then (110, 217) else (38, 131)))) else (if i.val < 4129 then (if i.val < 4127 then (if i.val < 4126 then (127, 162) else (62, 200)) else (if i.val < 4128 then (108, 156) else (85, 123))) else (if i.val < 4131 then (if i.val < 4130 then (85, 118) else (115, 223)) else (if i.val < 4132 then (105, 38) else (if i.val < 4133 then (109, 243) else (116, 209)))))) else (if i.val < 4142 then (if i.val < 4138 then (if i.val < 4136 then (if i.val < 4135 then (140, 145) else (134, 105)) else (if i.val < 4137 then (82, 222) else (110, 87))) else (if i.val < 4140 then (if i.val < 4139 then (138, 246) else (46, 236)) else (if i.val < 4141 then (138, 161) else (130, 2)))) else (if i.val < 4146 then (if i.val < 4144 then (if i.val < 4143 then (92, 123) else (61, 147)) else (if i.val < 4145 then (97, 27) else (126, 151))) else (if i.val < 4148 then (if i.val < 4147 then (66, 59) else (107, 65)) else (if i.val < 4149 then (140, 244) else (if i.val < 4150 then (131, 135) else (100, 116))))))) else (if i.val < 4168 then (if i.val < 4159 then (if i.val < 4155 then (if i.val < 4153 then (if i.val < 4152 then (19, 81) else (139, 134)) else (if i.val < 4154 then (116, 47) else (143, 222))) else (if i.val < 4157 then (if i.val < 4156 then (115, 172) else (120, 198)) else (if i.val < 4158 then (72, 137) else (38, 229)))) else (if i.val < 4163 then (if i.val < 4161 then (if i.val < 4160 then (93, 201) else (144, 43)) else (if i.val < 4162 then (83, 224) else (129, 208))) else (if i.val < 4165 then (if i.val < 4164 then (42, 144) else (83, 251)) else (if i.val < 4166 then (98, 78) else (if i.val < 4167 then (142, 231) else (144, 82)))))) else (if i.val < 4176 then (if i.val < 4172 then (if i.val < 4170 then (if i.val < 4169 then (110, 99) else (10, 0)) else (if i.val < 4171 then (135, 130) else (98, 245))) else (if i.val < 4174 then (if i.val < 4173 then (43, 239) else (139, 40)) else (if i.val < 4175 then (63, 160) else (54, 132)))) else (if i.val < 4180 then (if i.val < 4178 then (if i.val < 4177 then (125, 32) else (45, 60)) else (if i.val < 4179 then (143, 104) else (20, 191))) else (if i.val < 4182 then (if i.val < 4181 then (138, 111) else (111, 176)) else (if i.val < 4183 then (119, 10) else (if i.val < 4184 then (43, 135) else (82, 64))))))))) else (if i.val < 4252 then (if i.val < 4218 then (if i.val < 4201 then (if i.val < 4193 then (if i.val < 4189 then (if i.val < 4187 then (if i.val < 4186 then (128, 106) else (135, 211)) else (if i.val < 4188 then (89, 4) else (119, 130))) else (if i.val < 4191 then (if i.val < 4190 then (144, 137) else (136, 242)) else (if i.val < 4192 then (116, 237) else (144, 85)))) else (if i.val < 4197 then (if i.val < 4195 then (if i.val < 4194 then (136, 26) else (123, 96)) else (if i.val < 4196 then (140, 220) else (34, 255))) else (if i.val < 4199 then (if i.val < 4198 then (141, 209) else (119, 171)) else (if i.val < 4200 then (109, 55) else (97, 223))))) else (if i.val < 4209 then (if i.val < 4205 then (if i.val < 4203 then (if i.val < 4202 then (133, 215) else (83, 179)) else (if i.val < 4204 then (119, 166) else (112, 148))) else (if i.val < 4207 then (if i.val < 4206 then (73, 48) else (39, 180)) else (if i.val < 4208 then (39, 28) else (29, 91)))) else (if i.val < 4213 then (if i.val < 4211 then (if i.val < 4210 then (128, 101) else (123, 120)) else (if i.val < 4212 then (82, 165) else (117, 240))) else (if i.val < 4215 then (if i.val < 4214 then (134, 137) else (136, 80)) else (if i.val < 4216 then (71, 28) else (if i.val < 4217 then (129, 236) else (44, 101))))))) else (if i.val < 4235 then (if i.val < 4226 then (if i.val < 4222 then (if i.val < 4220 then (if i.val < 4219 then (74, 178) else (6, 13)) else (if i.val < 4221 then (110, 225) else (118, 158))) else (if i.val < 4224 then (if i.val < 4223 then (88, 126) else (142, 45)) else (if i.val < 4225 then (85, 163) else (71, 254)))) else (if i.val < 4230 then (if i.val < 4228 then (if i.val < 4227 then (134, 177) else (108, 29)) else (if i.val < 4229 then (124, 232) else (33, 244))) else (if i.val < 4232 then (if i.val < 4231 then (24, 152) else (35, 91)) else (if i.val < 4233 then (54, 33) else (if i.val < 4234 then (121, 16) else (142, 84)))))) else (if i.val < 4243 then (if i.val < 4239 then (if i.val < 4237 then (if i.val < 4236 then (105, 166) else (137, 117)) else (if i.val < 4238 then (56, 158) else (141, 234))) else (if i.val < 4241 then (if i.val < 4240 then (102, 241) else (124, 37)) else (if i.val < 4242 then (70, 207) else (140, 146)))) else (if i.val < 4247 then (if i.val < 4245 then (if i.val < 4244 then (42, 226) else (6, 131)) else (if i.val < 4246 then (45, 32) else (71, 229))) else (if i.val < 4249 then (if i.val < 4248 then (72, 3) else (33, 3)) else (if i.val < 4250 then (113, 25) else (if i.val < 4251 then (128, 121) else (91, 197)))))))) else (if i.val < 4286 then (if i.val < 4269 then (if i.val < 4260 then (if i.val < 4256 then (if i.val < 4254 then (if i.val < 4253 then (140, 98) else (111, 248)) else (if i.val < 4255 then (100, 184) else (119, 218))) else (if i.val < 4258 then (if i.val < 4257 then (91, 231) else (138, 67)) else (if i.val < 4259 then (123, 170) else (58, 115)))) else (if i.val < 4264 then (if i.val < 4262 then (if i.val < 4261 then (35, 6) else (125, 73)) else (if i.val < 4263 then (129, 12) else (125, 177))) else (if i.val < 4266 then (if i.val < 4265 then (57, 67) else (65, 147)) else (if i.val < 4267 then (106, 18) else (if i.val < 4268 then (103, 62) else (138, 62)))))) else (if i.val < 4277 then (if i.val < 4273 then (if i.val < 4271 then (if i.val < 4270 then (53, 166) else (98, 149)) else (if i.val < 4272 then (124, 182) else (21, 238))) else (if i.val < 4275 then (if i.val < 4274 then (130, 32) else (142, 105)) else (if i.val < 4276 then (126, 222) else (67, 241)))) else (if i.val < 4281 then (if i.val < 4279 then (if i.val < 4278 then (37, 154) else (135, 203)) else (if i.val < 4280 then (144, 98) else (138, 210))) else (if i.val < 4283 then (if i.val < 4282 then (136, 144) else (94, 95)) else (if i.val < 4284 then (139, 15) else (if i.val < 4285 then (144, 51) else (90, 186))))))) else (if i.val < 4303 then (if i.val < 4294 then (if i.val < 4290 then (if i.val < 4288 then (if i.val < 4287 then (133, 141) else (133, 200)) else (if i.val < 4289 then (107, 10) else (17, 93))) else (if i.val < 4292 then (if i.val < 4291 then (112, 190) else (115, 0)) else (if i.val < 4293 then (41, 107) else (129, 50)))) else (if i.val < 4298 then (if i.val < 4296 then (if i.val < 4295 then (140, 16) else (38, 216)) else (if i.val < 4297 then (0, 78) else (105, 255))) else (if i.val < 4300 then (if i.val < 4299 then (70, 89) else (123, 227)) else (if i.val < 4301 then (82, 30) else (if i.val < 4302 then (53, 142) else (137, 228)))))) else (if i.val < 4311 then (if i.val < 4307 then (if i.val < 4305 then (if i.val < 4304 then (0, 24) else (89, 239)) else (if i.val < 4306 then (19, 230) else (42, 101))) else (if i.val < 4309 then (if i.val < 4308 then (144, 142) else (33, 67)) else (if i.val < 4310 then (20, 222) else (104, 181)))) else (if i.val < 4315 then (if i.val < 4313 then (if i.val < 4312 then (28, 136) else (124, 38)) else (if i.val < 4314 then (70, 242) else (100, 27))) else (if i.val < 4317 then (if i.val < 4316 then (123, 157) else (100, 68)) else (if i.val < 4318 then (114, 215) else (if i.val < 4319 then (6, 177) else (103, 219))))))))))))))

def g32p_supplierGroup01_classify : Fin 4320 → Fin 102 :=
  fun i => (if i.val < 2160 then (if i.val < 1080 then (if i.val < 540 then (if i.val < 270 then (if i.val < 135 then (if i.val < 67 then (if i.val < 33 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 38) else (if i.val < 3 then 49 else 69)) else (if i.val < 6 then (if i.val < 5 then 49 else 49) else (if i.val < 7 then 34 else 38))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 49) else (if i.val < 11 then 30 else 49)) else (if i.val < 14 then (if i.val < 13 then 30 else 30) else (if i.val < 15 then 38 else 99)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 10 else 10) else (if i.val < 19 then 92 else 10)) else (if i.val < 22 then (if i.val < 21 then 34 else 92) else (if i.val < 23 then 40 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 92 else 34) else (if i.val < 27 then 40 else 92)) else (if i.val < 30 then (if i.val < 29 then 40 else 40) else (if i.val < 31 then 97 else (if i.val < 32 then 38 else 49)))))) else (if i.val < 50 then (if i.val < 41 then (if i.val < 37 then (if i.val < 35 then (if i.val < 34 then 49 else 30) else (if i.val < 36 then 49 else 30)) else (if i.val < 39 then (if i.val < 38 then 30 else 38) else (if i.val < 40 then 49 else 30))) else (if i.val < 45 then (if i.val < 43 then (if i.val < 42 then 30 else 38) else (if i.val < 44 then 30 else 38)) else (if i.val < 47 then (if i.val < 46 then 38 else 49) else (if i.val < 48 then 30 else (if i.val < 49 then 30 else 38))))) else (if i.val < 58 then (if i.val < 54 then (if i.val < 52 then (if i.val < 51 then 30 else 38) else (if i.val < 53 then 38 else 49)) else (if i.val < 56 then (if i.val < 55 then 30 else 38) else (if i.val < 57 then 38 else 49))) else (if i.val < 62 then (if i.val < 60 then (if i.val < 59 then 38 else 49) else (if i.val < 61 then 57 else 69)) else (if i.val < 64 then (if i.val < 63 then 49 else 49) else (if i.val < 65 then 34 else (if i.val < 66 then 49 else 57))))))) else (if i.val < 101 then (if i.val < 84 then (if i.val < 75 then (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then 34 else 38) else (if i.val < 70 then 49 else 34)) else (if i.val < 73 then (if i.val < 72 then 57 else 21) else (if i.val < 74 then 34 else 21))) else (if i.val < 79 then (if i.val < 77 then (if i.val < 76 then 38 else 13) else (if i.val < 78 then 57 else 34)) else (if i.val < 81 then (if i.val < 80 then 21 else 57) else (if i.val < 82 then 38 else (if i.val < 83 then 21 else 84))))) else (if i.val < 92 then (if i.val < 88 then (if i.val < 86 then (if i.val < 85 then 34 else 21) else (if i.val < 87 then 21 else 56)) else (if i.val < 90 then (if i.val < 89 then 38 else 84) else (if i.val < 91 then 57 else 57))) else (if i.val < 96 then (if i.val < 94 then (if i.val < 93 then 38 else 34) else (if i.val < 95 then 21 else 21)) else (if i.val < 98 then (if i.val < 97 then 13 else 57) else (if i.val < 99 then 21 else (if i.val < 100 then 38 else 84)))))) else (if i.val < 118 then (if i.val < 109 then (if i.val < 105 then (if i.val < 103 then (if i.val < 102 then 21 else 56) else (if i.val < 104 then 84 else 57)) else (if i.val < 107 then (if i.val < 106 then 38 else 21) else (if i.val < 108 then 13 else 21))) else (if i.val < 113 then (if i.val < 111 then (if i.val < 110 then 84 else 56) else (if i.val < 112 then 57 else 38)) else (if i.val < 115 then (if i.val < 114 then 13 else 84) else (if i.val < 116 then 57 else (if i.val < 117 then 69 else 38))))) else (if i.val < 126 then (if i.val < 122 then (if i.val < 120 then (if i.val < 119 then 49 else 49) else (if i.val < 121 then 30 else 49)) else (if i.val < 124 then (if i.val < 123 then 30 else 30) else (if i.val < 125 then 38 else 49))) else (if i.val < 130 then (if i.val < 128 then (if i.val < 127 then 30 else 30) else (if i.val < 129 then 73 else 30)) else (if i.val < 132 then (if i.val < 131 then 22 else 38) else (if i.val < 133 then 49 else (if i.val < 134 then 30 else 30)))))))) else (if i.val < 202 then (if i.val < 168 then (if i.val < 151 then (if i.val < 143 then (if i.val < 139 then (if i.val < 137 then (if i.val < 136 then 38 else 30) else (if i.val < 138 then 38 else 73)) else (if i.val < 141 then (if i.val < 140 then 10 else 30) else (if i.val < 142 then 38 else 22))) else (if i.val < 147 then (if i.val < 145 then (if i.val < 144 then 46 else 38) else (if i.val < 146 then 86 else 57)) else (if i.val < 149 then (if i.val < 148 then 30 else 22) else (if i.val < 150 then 30 else 38)))) else (if i.val < 159 then (if i.val < 155 then (if i.val < 153 then (if i.val < 152 then 38 else 86) else (if i.val < 154 then 30 else 38)) else (if i.val < 157 then (if i.val < 156 then 49 else 73) else (if i.val < 158 then 49 else 10))) else (if i.val < 163 then (if i.val < 161 then (if i.val < 160 then 57 else 73) else (if i.val < 162 then 38 else 46)) else (if i.val < 165 then (if i.val < 164 then 22 else 49) else (if i.val < 166 then 46 else (if i.val < 167 then 34 else 38)))))) else (if i.val < 185 then (if i.val < 176 then (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 10 else 86) else (if i.val < 171 then 34 else 21)) else (if i.val < 174 then (if i.val < 173 then 30 else 73) else (if i.val < 175 then 22 else 49))) else (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 30 else 38) else (if i.val < 179 then 10 else 38)) else (if i.val < 182 then (if i.val < 181 then 46 else 86) else (if i.val < 183 then 57 else (if i.val < 184 then 22 else 38))))) else (if i.val < 193 then (if i.val < 189 then (if i.val < 187 then (if i.val < 186 then 86 else 38) else (if i.val < 188 then 49 else 49)) else (if i.val < 191 then (if i.val < 190 then 57 else 73) else (if i.val < 192 then 46 else 49))) else (if i.val < 197 then (if i.val < 195 then (if i.val < 194 then 34 else 10) else (if i.val < 196 then 34 else 21)) else (if i.val < 199 then (if i.val < 198 then 73 else 49) else (if i.val < 200 then 38 else (if i.val < 201 then 10 else 46))))))) else (if i.val < 236 then (if i.val < 219 then (if i.val < 210 then (if i.val < 206 then (if i.val < 204 then (if i.val < 203 then 57 else 22) else (if i.val < 205 then 86 else 49)) else (if i.val < 208 then (if i.val < 207 then 57 else 46) else (if i.val < 209 then 34 else 34))) else (if i.val < 214 then (if i.val < 212 then (if i.val < 211 then 21 else 49) else (if i.val < 213 then 10 else 57)) else (if i.val < 216 then (if i.val < 215 then 86 else 57) else (if i.val < 217 then 34 else (if i.val < 218 then 21 else 49))))) else (if i.val < 227 then (if i.val < 223 then (if i.val < 221 then (if i.val < 220 then 86 else 86) else (if i.val < 222 then 4 else 86)) else (if i.val < 225 then (if i.val < 224 then 34 else 4) else (if i.val < 226 then 71 else 86))) else (if i.val < 231 then (if i.val < 229 then (if i.val < 228 then 4 else 34) else (if i.val < 230 then 71 else 4)) else (if i.val < 233 then (if i.val < 232 then 71 else 71) else (if i.val < 234 then 96 else (if i.val < 235 then 35 else 4)))))) else (if i.val < 253 then (if i.val < 244 then (if i.val < 240 then (if i.val < 238 then (if i.val < 237 then 38 else 34) else (if i.val < 239 then 40 else 71)) else (if i.val < 242 then (if i.val < 241 then 26 else 4) else (if i.val < 243 then 38 else 71))) else (if i.val < 248 then (if i.val < 246 then (if i.val < 245 then 47 else 71) else (if i.val < 247 then 26 else 15)) else (if i.val < 250 then (if i.val < 249 then 35 else 38) else (if i.val < 251 then 4 else (if i.val < 252 then 71 else 38))))) else (if i.val < 261 then (if i.val < 257 then (if i.val < 255 then (if i.val < 254 then 45 else 34) else (if i.val < 256 then 71 else 47)) else (if i.val < 259 then (if i.val < 258 then 71 else 56) else (if i.val < 260 then 26 else 15))) else (if i.val < 265 then (if i.val < 263 then (if i.val < 262 then 38 else 38) else (if i.val < 264 then 11 else 71)) else (if i.val < 267 then (if i.val < 266 then 47 else 47) else (if i.val < 268 then 57 else (if i.val < 269 then 71 else 45))))))))) else (if i.val < 405 then (if i.val < 337 then (if i.val < 303 then (if i.val < 286 then (if i.val < 278 then (if i.val < 274 then (if i.val < 272 then (if i.val < 271 then 26 else 57) else (if i.val < 273 then 78 else 35)) else (if i.val < 276 then (if i.val < 275 then 40 else 38) else (if i.val < 277 then 26 else 4))) else (if i.val < 282 then (if i.val < 280 then (if i.val < 279 then 71 else 56) else (if i.val < 281 then 38 else 47)) else (if i.val < 284 then (if i.val < 283 then 45 else 15) else (if i.val < 285 then 40 else 71)))) else (if i.val < 294 then (if i.val < 290 then (if i.val < 288 then (if i.val < 287 then 47 else 47) else (if i.val < 289 then 66 else 71)) else (if i.val < 292 then (if i.val < 291 then 47 else 56) else (if i.val < 293 then 15 else 26))) else (if i.val < 298 then (if i.val < 296 then (if i.val < 295 then 66 else 69) else (if i.val < 297 then 38 else 47)) else (if i.val < 300 then (if i.val < 299 then 38 else 47) else (if i.val < 301 then 11 else (if i.val < 302 then 57 else 71)))))) else (if i.val < 320 then (if i.val < 311 then (if i.val < 307 then (if i.val < 305 then (if i.val < 304 then 56 else 47) else (if i.val < 306 then 15 else 47)) else (if i.val < 309 then (if i.val < 308 then 15 else 57) else (if i.val < 310 then 78 else 26))) else (if i.val < 315 then (if i.val < 313 then (if i.val < 312 then 45 else 57) else (if i.val < 314 then 26 else 66)) else (if i.val < 317 then (if i.val < 316 then 57 else 6) else (if i.val < 318 then 10 else (if i.val < 319 then 35 else 38))))) else (if i.val < 328 then (if i.val < 324 then (if i.val < 322 then (if i.val < 321 then 40 else 26) else (if i.val < 323 then 38 else 47)) else (if i.val < 326 then (if i.val < 325 then 26 else 15) else (if i.val < 327 then 38 else 71))) else (if i.val < 332 then (if i.val < 330 then (if i.val < 329 then 47 else 56) else (if i.val < 331 then 15 else 38)) else (if i.val < 334 then (if i.val < 333 then 11 else 47) else (if i.val < 335 then 57 else (if i.val < 336 then 45 else 57))))))) else (if i.val < 371 then (if i.val < 354 then (if i.val < 345 then (if i.val < 341 then (if i.val < 339 then (if i.val < 338 then 78 else 40) else (if i.val < 340 then 26 else 71)) else (if i.val < 343 then (if i.val < 342 then 56 else 47) else (if i.val < 344 then 15 else 40))) else (if i.val < 349 then (if i.val < 347 then (if i.val < 346 then 47 else 66) else (if i.val < 348 then 47 else 15)) else (if i.val < 351 then (if i.val < 350 then 66 else 69) else (if i.val < 352 then 47 else (if i.val < 353 then 47 else 57))))) else (if i.val < 362 then (if i.val < 358 then (if i.val < 356 then (if i.val < 355 then 56 else 15) else (if i.val < 357 then 15 else 78)) else (if i.val < 360 then (if i.val < 359 then 26 else 57) else (if i.val < 361 then 66 else 6))) else (if i.val < 366 then (if i.val < 364 then (if i.val < 363 then 10 else 38) else (if i.val < 365 then 26 else 47)) else (if i.val < 368 then (if i.val < 367 then 15 else 38) else (if i.val < 369 then 47 else (if i.val < 370 then 15 else 11)))))) else (if i.val < 388 then (if i.val < 379 then (if i.val < 375 then (if i.val < 373 then (if i.val < 372 then 57 else 57) else (if i.val < 374 then 78 else 26)) else (if i.val < 377 then (if i.val < 376 then 56 else 15) else (if i.val < 378 then 47 else 66))) else (if i.val < 383 then (if i.val < 381 then (if i.val < 380 then 15 else 69) else (if i.val < 382 then 47 else 57)) else (if i.val < 385 then (if i.val < 384 then 15 else 78) else (if i.val < 386 then 57 else (if i.val < 387 then 6 else 10))))) else (if i.val < 396 then (if i.val < 392 then (if i.val < 390 then (if i.val < 389 then 26 else 15) else (if i.val < 391 then 45 else 15)) else (if i.val < 394 then (if i.val < 393 then 57 else 78) else (if i.val < 395 then 26 else 15))) else (if i.val < 400 then (if i.val < 398 then (if i.val < 397 then 66 else 69) else (if i.val < 399 then 57 else 78)) else (if i.val < 402 then (if i.val < 401 then 6 else 10) else (if i.val < 403 then 101 else (if i.val < 404 then 49 else 30)))))))) else (if i.val < 472 then (if i.val < 438 then (if i.val < 421 then (if i.val < 413 then (if i.val < 409 then (if i.val < 407 then (if i.val < 406 then 49 else 30) else (if i.val < 408 then 30 else 38)) else (if i.val < 411 then (if i.val < 410 then 49 else 30) else (if i.val < 412 then 30 else 38))) else (if i.val < 417 then (if i.val < 415 then (if i.val < 414 then 30 else 38) else (if i.val < 416 then 38 else 49)) else (if i.val < 419 then (if i.val < 418 then 30 else 30) else (if i.val < 420 then 38 else 30)))) else (if i.val < 429 then (if i.val < 425 then (if i.val < 423 then (if i.val < 422 then 38 else 38) else (if i.val < 424 then 49 else 30)) else (if i.val < 427 then (if i.val < 426 then 38 else 38) else (if i.val < 428 then 49 else 38))) else (if i.val < 433 then (if i.val < 431 then (if i.val < 430 then 49 else 57) else (if i.val < 432 then 30 else 69)) else (if i.val < 435 then (if i.val < 434 then 30 else 73) else (if i.val < 436 then 38 else (if i.val < 437 then 10 else 30)))))) else (if i.val < 455 then (if i.val < 446 then (if i.val < 442 then (if i.val < 440 then (if i.val < 439 then 22 else 86) else (if i.val < 441 then 38 else 13)) else (if i.val < 444 then (if i.val < 443 then 49 else 57) else (if i.val < 445 then 69 else 38))) else (if i.val < 450 then (if i.val < 448 then (if i.val < 447 then 46 else 38) else (if i.val < 449 then 10 else 49)) else (if i.val < 452 then (if i.val < 451 then 60 else 86) else (if i.val < 453 then 49 else (if i.val < 454 then 16 else 21))))) else (if i.val < 463 then (if i.val < 459 then (if i.val < 457 then (if i.val < 456 then 30 else 22) else (if i.val < 458 then 86 else 30)) else (if i.val < 461 then (if i.val < 460 then 73 else 10) else (if i.val < 462 then 38 else 86))) else (if i.val < 467 then (if i.val < 465 then (if i.val < 464 then 10 else 57) else (if i.val < 466 then 73 else 22)) else (if i.val < 469 then (if i.val < 468 then 46 else 86) else (if i.val < 470 then 16 else (if i.val < 471 then 38 else 10))))))) else (if i.val < 506 then (if i.val < 489 then (if i.val < 480 then (if i.val < 476 then (if i.val < 474 then (if i.val < 473 then 13 else 35) else (if i.val < 475 then 49 else 57)) else (if i.val < 478 then (if i.val < 477 then 21 else 69) else (if i.val < 479 then 46 else 38))) else (if i.val < 484 then (if i.val < 482 then (if i.val < 481 then 46 else 46) else (if i.val < 483 then 57 else 38)) else (if i.val < 486 then (if i.val < 485 then 86 else 10) else (if i.val < 487 then 34 else (if i.val < 488 then 49 else 32))))) else (if i.val < 497 then (if i.val < 493 then (if i.val < 491 then (if i.val < 490 then 60 else 21) else (if i.val < 492 then 10 else 86)) else (if i.val < 495 then (if i.val < 494 then 57 else 49) else (if i.val < 496 then 60 else 16))) else (if i.val < 501 then (if i.val < 499 then (if i.val < 498 then 21 else 49) else (if i.val < 500 then 30 else 73)) else (if i.val < 503 then (if i.val < 502 then 22 else 13) else (if i.val < 504 then 69 else (if i.val < 505 then 10 else 86)))))) else (if i.val < 523 then (if i.val < 514 then (if i.val < 510 then (if i.val < 508 then (if i.val < 507 then 57 else 22) else (if i.val < 509 then 73 else 49)) else (if i.val < 512 then (if i.val < 511 then 10 else 57) else (if i.val < 513 then 38 else 46))) else (if i.val < 518 then (if i.val < 516 then (if i.val < 515 then 86 else 32) else (if i.val < 517 then 10 else 60)) else (if i.val < 520 then (if i.val < 519 then 21 else 73) else (if i.val < 521 then 10 else (if i.val < 522 then 22 else 49))))) else (if i.val < 531 then (if i.val < 527 then (if i.val < 525 then (if i.val < 524 then 46 else 60) else (if i.val < 526 then 86 else 57)) else (if i.val < 529 then (if i.val < 528 then 16 else 21) else (if i.val < 530 then 86 else 10))) else (if i.val < 535 then (if i.val < 533 then (if i.val < 532 then 34 else 13) else (if i.val < 534 then 57 else 35)) else (if i.val < 537 then (if i.val < 536 then 38 else 49) else (if i.val < 538 then 16 else (if i.val < 539 then 38 else 49)))))))))) else (if i.val < 810 then (if i.val < 675 then (if i.val < 607 then (if i.val < 573 then (if i.val < 556 then (if i.val < 548 then (if i.val < 544 then (if i.val < 542 then (if i.val < 541 then 69 else 86) else (if i.val < 543 then 46 else 16)) else (if i.val < 546 then (if i.val < 545 then 38 else 46) else (if i.val < 547 then 35 else 46))) else (if i.val < 552 then (if i.val < 550 then (if i.val < 549 then 34 else 57) else (if i.val < 551 then 21 else 13)) else (if i.val < 554 then (if i.val < 553 then 86 else 32) else (if i.val < 555 then 10 else 57)))) else (if i.val < 564 then (if i.val < 560 then (if i.val < 558 then (if i.val < 557 then 34 else 38) else (if i.val < 559 then 49 else 35)) else (if i.val < 562 then (if i.val < 561 then 32 else 69) else (if i.val < 563 then 60 else 38))) else (if i.val < 568 then (if i.val < 566 then (if i.val < 565 then 49 else 10) else (if i.val < 567 then 60 else 86)) else (if i.val < 570 then (if i.val < 569 then 16 else 57) else (if i.val < 571 then 21 else (if i.val < 572 then 49 else 57)))))) else (if i.val < 590 then (if i.val < 581 then (if i.val < 577 then (if i.val < 575 then (if i.val < 574 then 60 else 38) else (if i.val < 576 then 16 else 38)) else (if i.val < 579 then (if i.val < 578 then 21 else 49) else (if i.val < 580 then 57 else 69))) else (if i.val < 585 then (if i.val < 583 then (if i.val < 582 then 73 else 10) else (if i.val < 584 then 22 else 86)) else (if i.val < 587 then (if i.val < 586 then 57 else 69) else (if i.val < 588 then 46 else (if i.val < 589 then 10 else 60))))) else (if i.val < 598 then (if i.val < 594 then (if i.val < 592 then (if i.val < 591 then 86 else 16) else (if i.val < 593 then 21 else 22)) else (if i.val < 596 then (if i.val < 595 then 86 else 73) else (if i.val < 597 then 46 else 16))) else (if i.val < 602 then (if i.val < 600 then (if i.val < 599 then 10 else 57) else (if i.val < 601 then 21 else 46)) else (if i.val < 604 then (if i.val < 603 then 46 else 57) else (if i.val < 605 then 86 else (if i.val < 606 then 34 else 32))))))) else (if i.val < 641 then (if i.val < 624 then (if i.val < 615 then (if i.val < 611 then (if i.val < 609 then (if i.val < 608 then 21 else 10) else (if i.val < 610 then 57 else 60)) else (if i.val < 613 then (if i.val < 612 then 21 else 49) else (if i.val < 614 then 73 else 13))) else (if i.val < 619 then (if i.val < 617 then (if i.val < 616 then 10 else 57) else (if i.val < 618 then 22 else 49)) else (if i.val < 621 then (if i.val < 620 then 57 else 46) else (if i.val < 622 then 32 else (if i.val < 623 then 60 else 21))))) else (if i.val < 632 then (if i.val < 628 then (if i.val < 626 then (if i.val < 625 then 10 else 49) else (if i.val < 627 then 60 else 57)) else (if i.val < 630 then (if i.val < 629 then 21 else 86) else (if i.val < 631 then 34 else 16))) else (if i.val < 636 then (if i.val < 634 then (if i.val < 633 then 38 else 49) else (if i.val < 635 then 86 else 16)) else (if i.val < 638 then (if i.val < 637 then 10 else 35) else (if i.val < 639 then 34 else (if i.val < 640 then 21 else 13)))))) else (if i.val < 658 then (if i.val < 649 then (if i.val < 645 then (if i.val < 643 then (if i.val < 642 then 32 else 57) else (if i.val < 644 then 38 else 35)) else (if i.val < 647 then (if i.val < 646 then 69 else 49) else (if i.val < 648 then 60 else 16))) else (if i.val < 653 then (if i.val < 651 then (if i.val < 650 then 21 else 57) else (if i.val < 652 then 38 else 49)) else (if i.val < 655 then (if i.val < 654 then 57 else 69) else (if i.val < 656 then 10 else (if i.val < 657 then 86 else 57))))) else (if i.val < 666 then (if i.val < 662 then (if i.val < 660 then (if i.val < 659 then 46 else 60) else (if i.val < 661 then 16 else 21)) else (if i.val < 664 then (if i.val < 663 then 86 else 46) else (if i.val < 665 then 16 else 35))) else (if i.val < 670 then (if i.val < 668 then (if i.val < 667 then 21 else 46) else (if i.val < 669 then 57 else 34)) else (if i.val < 672 then (if i.val < 671 then 21 else 57) else (if i.val < 673 then 21 else (if i.val < 674 then 49 else 13)))))))) else (if i.val < 742 then (if i.val < 708 then (if i.val < 691 then (if i.val < 683 then (if i.val < 679 then (if i.val < 677 then (if i.val < 676 then 57 else 86) else (if i.val < 678 then 57 else 32)) else (if i.val < 681 then (if i.val < 680 then 21 else 10) else (if i.val < 682 then 60 else 21))) else (if i.val < 687 then (if i.val < 685 then (if i.val < 684 then 34 else 38) else (if i.val < 686 then 38 else 49)) else (if i.val < 689 then (if i.val < 688 then 16 else 35) else (if i.val < 690 then 21 else 32)))) else (if i.val < 699 then (if i.val < 695 then (if i.val < 693 then (if i.val < 692 then 38 else 69) else (if i.val < 694 then 49 else 60)) else (if i.val < 697 then (if i.val < 696 then 38 else 57) else (if i.val < 698 then 10 else 57))) else (if i.val < 703 then (if i.val < 701 then (if i.val < 700 then 60 else 21) else (if i.val < 702 then 86 else 16)) else (if i.val < 705 then (if i.val < 704 then 21 else 57) else (if i.val < 706 then 21 else (if i.val < 707 then 21 else 49)))))) else (if i.val < 725 then (if i.val < 716 then (if i.val < 712 then (if i.val < 710 then (if i.val < 709 then 57 else 21) else (if i.val < 711 then 60 else 21)) else (if i.val < 714 then (if i.val < 713 then 38 else 49) else (if i.val < 715 then 16 else 21))) else (if i.val < 720 then (if i.val < 718 then (if i.val < 717 then 38 else 49) else (if i.val < 719 then 21 else 49)) else (if i.val < 722 then (if i.val < 721 then 57 else 38) else (if i.val < 723 then 49 else (if i.val < 724 then 57 else 34))))) else (if i.val < 733 then (if i.val < 729 then (if i.val < 727 then (if i.val < 726 then 49 else 34) else (if i.val < 728 then 57 else 21)) else (if i.val < 731 then (if i.val < 730 then 34 else 21) else (if i.val < 732 then 38 else 13))) else (if i.val < 737 then (if i.val < 735 then (if i.val < 734 then 57 else 34) else (if i.val < 736 then 21 else 57)) else (if i.val < 739 then (if i.val < 738 then 45 else 34) else (if i.val < 740 then 21 else (if i.val < 741 then 21 else 11))))))) else (if i.val < 776 then (if i.val < 759 then (if i.val < 750 then (if i.val < 746 then (if i.val < 744 then (if i.val < 743 then 38 else 45) else (if i.val < 745 then 57 else 57)) else (if i.val < 748 then (if i.val < 747 then 38 else 34) else (if i.val < 749 then 21 else 21))) else (if i.val < 754 then (if i.val < 752 then (if i.val < 751 then 13 else 57) else (if i.val < 753 then 21 else 45)) else (if i.val < 756 then (if i.val < 755 then 21 else 11) else (if i.val < 757 then 45 else (if i.val < 758 then 57 else 38))))) else (if i.val < 767 then (if i.val < 763 then (if i.val < 761 then (if i.val < 760 then 21 else 13) else (if i.val < 762 then 21 else 45)) else (if i.val < 765 then (if i.val < 764 then 11 else 57) else (if i.val < 766 then 13 else 45))) else (if i.val < 771 then (if i.val < 769 then (if i.val < 768 then 57 else 69) else (if i.val < 770 then 18 else 84)) else (if i.val < 773 then (if i.val < 772 then 34 else 21) else (if i.val < 774 then 49 else (if i.val < 775 then 21 else 13)))))) else (if i.val < 793 then (if i.val < 784 then (if i.val < 780 then (if i.val < 778 then (if i.val < 777 then 57 else 18) else (if i.val < 779 then 21 else 26)) else (if i.val < 782 then (if i.val < 781 then 45 else 30) else (if i.val < 783 then 21 else 11))) else (if i.val < 788 then (if i.val < 786 then (if i.val < 785 then 66 else 45) else (if i.val < 787 then 15 else 38)) else (if i.val < 790 then (if i.val < 789 then 38 else 56) else (if i.val < 791 then 21 else (if i.val < 792 then 26 else 13))))) else (if i.val < 801 then (if i.val < 797 then (if i.val < 795 then (if i.val < 794 then 30 else 49) else (if i.val < 796 then 45 else 15)) else (if i.val < 799 then (if i.val < 798 then 11 else 66) else (if i.val < 800 then 57 else 69))) else (if i.val < 805 then (if i.val < 803 then (if i.val < 802 then 13 else 30) else (if i.val < 804 then 45 else 30)) else (if i.val < 807 then (if i.val < 806 then 38 else 49) else (if i.val < 808 then 57 else (if i.val < 809 then 38 else 18))))))))) else (if i.val < 945 then (if i.val < 877 then (if i.val < 843 then (if i.val < 826 then (if i.val < 818 then (if i.val < 814 then (if i.val < 812 then (if i.val < 811 then 47 else 84) else (if i.val < 813 then 57 else 38)) else (if i.val < 816 then (if i.val < 815 then 21 else 84) else (if i.val < 817 then 49 else 30))) else (if i.val < 822 then (if i.val < 820 then (if i.val < 819 then 21 else 13) else (if i.val < 821 then 47 else 65)) else (if i.val < 824 then (if i.val < 823 then 13 else 30) else (if i.val < 825 then 69 else 18)))) else (if i.val < 834 then (if i.val < 830 then (if i.val < 828 then (if i.val < 827 then 26 else 21) else (if i.val < 829 then 26 else 65)) else (if i.val < 832 then (if i.val < 831 then 45 else 30) else (if i.val < 833 then 30 else 38))) else (if i.val < 838 then (if i.val < 836 then (if i.val < 835 then 49 else 47) else (if i.val < 837 then 57 else 11)) else (if i.val < 840 then (if i.val < 839 then 30 else 66) else (if i.val < 841 then 22 else (if i.val < 842 then 45 else 30)))))) else (if i.val < 860 then (if i.val < 851 then (if i.val < 847 then (if i.val < 845 then (if i.val < 844 then 73 else 46) else (if i.val < 846 then 38 else 26)) else (if i.val < 849 then (if i.val < 848 then 56 else 30) else (if i.val < 850 then 21 else 26))) else (if i.val < 855 then (if i.val < 853 then (if i.val < 852 then 57 else 13) else (if i.val < 854 then 57 else 30)) else (if i.val < 857 then (if i.val < 856 then 69 else 47) else (if i.val < 858 then 57 else (if i.val < 859 then 45 else 57))))) else (if i.val < 868 then (if i.val < 864 then (if i.val < 862 then (if i.val < 861 then 15 else 73) else (if i.val < 863 then 11 else 65)) else (if i.val < 866 then (if i.val < 865 then 66 else 24) else (if i.val < 867 then 57 else 73))) else (if i.val < 872 then (if i.val < 870 then (if i.val < 869 then 46 else 84) else (if i.val < 871 then 30 else 13)) else (if i.val < 874 then (if i.val < 873 then 65 else 30) else (if i.val < 875 then 69 else (if i.val < 876 then 45 else 30))))))) else (if i.val < 911 then (if i.val < 894 then (if i.val < 885 then (if i.val < 881 then (if i.val < 879 then (if i.val < 878 then 30 else 73) else (if i.val < 880 then 57 else 22)) else (if i.val < 883 then (if i.val < 882 then 38 else 49) else (if i.val < 884 then 34 else 18))) else (if i.val < 889 then (if i.val < 887 then (if i.val < 886 then 38 else 47) else (if i.val < 888 then 18 else 13)) else (if i.val < 891 then (if i.val < 890 then 15 else 38) else (if i.val < 892 then 26 else (if i.val < 893 then 49 else 66))))) else (if i.val < 902 then (if i.val < 898 then (if i.val < 896 then (if i.val < 895 then 84 else 30) else (if i.val < 897 then 38 else 38)) else (if i.val < 900 then (if i.val < 899 then 49 else 21) else (if i.val < 901 then 56 else 30))) else (if i.val < 906 then (if i.val < 904 then (if i.val < 903 then 49 else 30) else (if i.val < 905 then 69 else 26)) else (if i.val < 908 then (if i.val < 907 then 13 else 57) else (if i.val < 909 then 47 else (if i.val < 910 then 57 else 65)))))) else (if i.val < 928 then (if i.val < 919 then (if i.val < 915 then (if i.val < 913 then (if i.val < 912 then 73 else 13) else (if i.val < 914 then 65 else 30)) else (if i.val < 917 then (if i.val < 916 then 22 else 46) else (if i.val < 918 then 18 else 13))) else (if i.val < 923 then (if i.val < 921 then (if i.val < 920 then 26 else 30) else (if i.val < 922 then 21 else 56)) else (if i.val < 925 then (if i.val < 924 then 30 else 26) else (if i.val < 926 then 57 else (if i.val < 927 then 65 else 38))))) else (if i.val < 936 then (if i.val < 932 then (if i.val < 930 then (if i.val < 929 then 45 else 57) else (if i.val < 931 then 30 else 69)) else (if i.val < 934 then (if i.val < 933 then 49 else 49) else (if i.val < 935 then 15 else 47))) else (if i.val < 940 then (if i.val < 938 then (if i.val < 937 then 57 else 57) else (if i.val < 939 then 11 else 30)) else (if i.val < 942 then (if i.val < 941 then 30 else 69) else (if i.val < 943 then 66 else (if i.val < 944 then 38 else 46)))))))) else (if i.val < 1012 then (if i.val < 978 then (if i.val < 961 then (if i.val < 953 then (if i.val < 949 then (if i.val < 947 then (if i.val < 946 then 30 else 30) else (if i.val < 948 then 73 else 73)) else (if i.val < 951 then (if i.val < 950 then 10 else 35) else (if i.val < 952 then 38 else 49))) else (if i.val < 957 then (if i.val < 955 then (if i.val < 954 then 26 else 66) else (if i.val < 956 then 56 else 15)) else (if i.val < 959 then (if i.val < 958 then 30 else 69) else (if i.val < 960 then 47 else 26)))) else (if i.val < 969 then (if i.val < 965 then (if i.val < 963 then (if i.val < 962 then 57 else 57) else (if i.val < 964 then 73 else 13)) else (if i.val < 967 then (if i.val < 966 then 57 else 57) else (if i.val < 968 then 24 else 30))) else (if i.val < 973 then (if i.val < 971 then (if i.val < 970 then 73 else 46) else (if i.val < 972 then 47 else 66)) else (if i.val < 975 then (if i.val < 974 then 49 else 30) else (if i.val < 976 then 57 else (if i.val < 977 then 22 else 45)))))) else (if i.val < 995 then (if i.val < 986 then (if i.val < 982 then (if i.val < 980 then (if i.val < 979 then 30 else 38) else (if i.val < 981 then 15 else 69)) else (if i.val < 984 then (if i.val < 983 then 73 else 46) else (if i.val < 985 then 66 else 65))) else (if i.val < 990 then (if i.val < 988 then (if i.val < 987 then 24 else 66) else (if i.val < 989 then 38 else 24)) else (if i.val < 992 then (if i.val < 991 then 86 else 73) else (if i.val < 993 then 4 else (if i.val < 994 then 84 else 30))))) else (if i.val < 1003 then (if i.val < 999 then (if i.val < 997 then (if i.val < 996 then 30 else 38) else (if i.val < 998 then 13 else 65)) else (if i.val < 1001 then (if i.val < 1000 then 22 else 30) else (if i.val < 1002 then 73 else 69))) else (if i.val < 1007 then (if i.val < 1005 then (if i.val < 1004 then 49 else 15) else (if i.val < 1006 then 73 else 30)) else (if i.val < 1009 then (if i.val < 1008 then 69 else 73) else (if i.val < 1010 then 10 else (if i.val < 1011 then 57 else 73))))))) else (if i.val < 1046 then (if i.val < 1029 then (if i.val < 1020 then (if i.val < 1016 then (if i.val < 1014 then (if i.val < 1013 then 22 else 86) else (if i.val < 1015 then 38 else 10)) else (if i.val < 1018 then (if i.val < 1017 then 35 else 38) else (if i.val < 1019 then 18 else 84))) else (if i.val < 1024 then (if i.val < 1022 then (if i.val < 1021 then 38 else 49) else (if i.val < 1023 then 47 else 57)) else (if i.val < 1026 then (if i.val < 1025 then 18 else 26) else (if i.val < 1027 then 30 else (if i.val < 1028 then 15 else 38))))) else (if i.val < 1037 then (if i.val < 1033 then (if i.val < 1031 then (if i.val < 1030 then 56 else 26) else (if i.val < 1032 then 30 else 49)) else (if i.val < 1035 then (if i.val < 1034 then 15 else 66) else (if i.val < 1036 then 69 else 30))) else (if i.val < 1041 then (if i.val < 1039 then (if i.val < 1038 then 30 else 49) else (if i.val < 1040 then 38 else 47)) else (if i.val < 1043 then (if i.val < 1042 then 57 else 26) else (if i.val < 1044 then 56 else (if i.val < 1045 then 30 else 38)))))) else (if i.val < 1063 then (if i.val < 1054 then (if i.val < 1050 then (if i.val < 1048 then (if i.val < 1047 then 49 else 57) else (if i.val < 1049 then 30 else 73)) else (if i.val < 1052 then (if i.val < 1051 then 46 else 26) else (if i.val < 1053 then 30 else 13))) else (if i.val < 1058 then (if i.val < 1056 then (if i.val < 1055 then 57 else 57) else (if i.val < 1057 then 69 else 57)) else (if i.val < 1060 then (if i.val < 1059 then 57 else 73) else (if i.val < 1061 then 65 else (if i.val < 1062 then 24 else 73))))) else (if i.val < 1071 then (if i.val < 1067 then (if i.val < 1065 then (if i.val < 1064 then 46 else 30) else (if i.val < 1066 then 65 else 69)) else (if i.val < 1069 then (if i.val < 1068 then 30 else 73) else (if i.val < 1070 then 22 else 49))) else (if i.val < 1075 then (if i.val < 1073 then (if i.val < 1072 then 34 else 18) else (if i.val < 1074 then 47 else 13)) else (if i.val < 1077 then (if i.val < 1076 then 15 else 26) else (if i.val < 1078 then 66 else (if i.val < 1079 then 30 else 38))))))))))) else (if i.val < 1620 then (if i.val < 1350 then (if i.val < 1215 then (if i.val < 1147 then (if i.val < 1113 then (if i.val < 1096 then (if i.val < 1088 then (if i.val < 1084 then (if i.val < 1082 then (if i.val < 1081 then 49 else 30) else (if i.val < 1083 then 30 else 69)) else (if i.val < 1086 then (if i.val < 1085 then 26 else 57) else (if i.val < 1087 then 57 else 73))) else (if i.val < 1092 then (if i.val < 1090 then (if i.val < 1089 then 65 else 22) else (if i.val < 1091 then 46 else 13)) else (if i.val < 1094 then (if i.val < 1093 then 30 else 84) else (if i.val < 1095 then 30 else 57)))) else (if i.val < 1104 then (if i.val < 1100 then (if i.val < 1098 then (if i.val < 1097 then 38 else 57) else (if i.val < 1099 then 38 else 69)) else (if i.val < 1102 then (if i.val < 1101 then 49 else 15) else (if i.val < 1103 then 57 else 73))) else (if i.val < 1108 then (if i.val < 1106 then (if i.val < 1105 then 30 else 73) else (if i.val < 1107 then 10 else 35)) else (if i.val < 1110 then (if i.val < 1109 then 49 else 66) else (if i.val < 1111 then 15 else (if i.val < 1112 then 69 else 57)))))) else (if i.val < 1130 then (if i.val < 1121 then (if i.val < 1117 then (if i.val < 1115 then (if i.val < 1114 then 73 else 57) else (if i.val < 1116 then 24 else 46)) else (if i.val < 1119 then (if i.val < 1118 then 66 else 30) else (if i.val < 1120 then 22 else 30))) else (if i.val < 1125 then (if i.val < 1123 then (if i.val < 1122 then 38 else 69) else (if i.val < 1124 then 46 else 66)) else (if i.val < 1127 then (if i.val < 1126 then 24 else 38) else (if i.val < 1128 then 4 else (if i.val < 1129 then 30 else 38))))) else (if i.val < 1138 then (if i.val < 1134 then (if i.val < 1132 then (if i.val < 1131 then 30 else 22) else (if i.val < 1133 then 73 else 49)) else (if i.val < 1136 then (if i.val < 1135 then 15 else 73) else (if i.val < 1137 then 73 else 86))) else (if i.val < 1142 then (if i.val < 1140 then (if i.val < 1139 then 10 else 35) else (if i.val < 1141 then 38 else 84)) else (if i.val < 1144 then (if i.val < 1143 then 49 else 57) else (if i.val < 1145 then 26 else (if i.val < 1146 then 30 else 38))))))) else (if i.val < 1181 then (if i.val < 1164 then (if i.val < 1155 then (if i.val < 1151 then (if i.val < 1149 then (if i.val < 1148 then 56 else 30) else (if i.val < 1150 then 15 else 69)) else (if i.val < 1153 then (if i.val < 1152 then 30 else 38) else (if i.val < 1154 then 49 else 47))) else (if i.val < 1159 then (if i.val < 1157 then (if i.val < 1156 then 57 else 26) else (if i.val < 1158 then 57 else 73)) else (if i.val < 1161 then (if i.val < 1160 then 46 else 30) else (if i.val < 1162 then 57 else (if i.val < 1163 then 57 else 73))))) else (if i.val < 1172 then (if i.val < 1168 then (if i.val < 1166 then (if i.val < 1165 then 24 else 46) else (if i.val < 1167 then 30 else 69)) else (if i.val < 1170 then (if i.val < 1169 then 73 else 49) else (if i.val < 1171 then 47 else 15))) else (if i.val < 1176 then (if i.val < 1174 then (if i.val < 1173 then 66 else 49) else (if i.val < 1175 then 69 else 57)) else (if i.val < 1178 then (if i.val < 1177 then 73 else 22) else (if i.val < 1179 then 46 else (if i.val < 1180 then 30 else 30)))))) else (if i.val < 1198 then (if i.val < 1189 then (if i.val < 1185 then (if i.val < 1183 then (if i.val < 1182 then 38 else 38) else (if i.val < 1184 then 49 else 15)) else (if i.val < 1187 then (if i.val < 1186 then 73 else 73) else (if i.val < 1188 then 10 else 35))) else (if i.val < 1193 then (if i.val < 1191 then (if i.val < 1190 then 66 else 69) else (if i.val < 1192 then 65 else 73)) else (if i.val < 1195 then (if i.val < 1194 then 24 else 46) else (if i.val < 1196 then 66 else (if i.val < 1197 then 22 else 38))))) else (if i.val < 1206 then (if i.val < 1202 then (if i.val < 1200 then (if i.val < 1199 then 46 else 24) else (if i.val < 1201 then 86 else 4)) else (if i.val < 1204 then (if i.val < 1203 then 38 else 73) else (if i.val < 1205 then 38 else 84))) else (if i.val < 1210 then (if i.val < 1208 then (if i.val < 1207 then 57 else 30) else (if i.val < 1209 then 38 else 30)) else (if i.val < 1212 then (if i.val < 1211 then 38 else 49) else (if i.val < 1213 then 57 else (if i.val < 1214 then 65 else 38)))))))) else (if i.val < 1282 then (if i.val < 1248 then (if i.val < 1231 then (if i.val < 1223 then (if i.val < 1219 then (if i.val < 1217 then (if i.val < 1216 then 22 else 46) else (if i.val < 1218 then 30 else 69)) else (if i.val < 1221 then (if i.val < 1220 then 73 else 46) else (if i.val < 1222 then 49 else 34))) else (if i.val < 1227 then (if i.val < 1225 then (if i.val < 1224 then 15 else 38) else (if i.val < 1226 then 73 else 46)) else (if i.val < 1229 then (if i.val < 1228 then 30 else 38) else (if i.val < 1230 then 49 else 46)))) else (if i.val < 1239 then (if i.val < 1235 then (if i.val < 1233 then (if i.val < 1232 then 10 else 35) else (if i.val < 1234 then 69 else 73)) else (if i.val < 1237 then (if i.val < 1236 then 46 else 22) else (if i.val < 1238 then 46 else 86))) else (if i.val < 1243 then (if i.val < 1241 then (if i.val < 1240 then 38 else 10) else (if i.val < 1242 then 38 else 49)) else (if i.val < 1245 then (if i.val < 1244 then 30 else 30) else (if i.val < 1246 then 22 else (if i.val < 1247 then 30 else 30)))))) else (if i.val < 1265 then (if i.val < 1256 then (if i.val < 1252 then (if i.val < 1250 then (if i.val < 1249 then 30 else 38) else (if i.val < 1251 then 30 else 86)) else (if i.val < 1254 then (if i.val < 1253 then 30 else 38) else (if i.val < 1255 then 73 else 46))) else (if i.val < 1260 then (if i.val < 1258 then (if i.val < 1257 then 38 else 10) else (if i.val < 1259 then 57 else 30)) else (if i.val < 1262 then (if i.val < 1261 then 73 else 30) else (if i.val < 1263 then 38 else (if i.val < 1264 then 38 else 10))))) else (if i.val < 1273 then (if i.val < 1269 then (if i.val < 1267 then (if i.val < 1266 then 30 else 38) else (if i.val < 1268 then 86 else 57)) else (if i.val < 1271 then (if i.val < 1270 then 22 else 38) else (if i.val < 1272 then 46 else 73))) else (if i.val < 1277 then (if i.val < 1275 then (if i.val < 1274 then 49 else 46) else (if i.val < 1276 then 86 else 10)) else (if i.val < 1279 then (if i.val < 1278 then 34 else 21) else (if i.val < 1280 then 22 else (if i.val < 1281 then 30 else 38))))))) else (if i.val < 1316 then (if i.val < 1299 then (if i.val < 1290 then (if i.val < 1286 then (if i.val < 1284 then (if i.val < 1283 then 86 else 38) else (if i.val < 1285 then 10 else 57)) else (if i.val < 1288 then (if i.val < 1287 then 73 else 38) else (if i.val < 1289 then 10 else 57))) else (if i.val < 1294 then (if i.val < 1292 then (if i.val < 1291 then 22 else 49) else (if i.val < 1293 then 34 else 86)) else (if i.val < 1296 then (if i.val < 1295 then 34 else 21) else (if i.val < 1297 then 22 else (if i.val < 1298 then 49 else 38))))) else (if i.val < 1307 then (if i.val < 1303 then (if i.val < 1301 then (if i.val < 1300 then 86 else 46) else (if i.val < 1302 then 57 else 10)) else (if i.val < 1305 then (if i.val < 1304 then 57 else 46) else (if i.val < 1306 then 34 else 34))) else (if i.val < 1311 then (if i.val < 1309 then (if i.val < 1308 then 21 else 86) else (if i.val < 1310 then 57 else 10)) else (if i.val < 1313 then (if i.val < 1312 then 57 else 21) else (if i.val < 1314 then 49 else (if i.val < 1315 then 22 else 46)))))) else (if i.val < 1333 then (if i.val < 1324 then (if i.val < 1320 then (if i.val < 1318 then (if i.val < 1317 then 49 else 57) else (if i.val < 1319 then 69 else 38)) else (if i.val < 1322 then (if i.val < 1321 then 10 else 86) else (if i.val < 1323 then 16 else 46))) else (if i.val < 1328 then (if i.val < 1326 then (if i.val < 1325 then 10 else 92) else (if i.val < 1327 then 21 else 73)) else (if i.val < 1330 then (if i.val < 1329 then 46 else 38) else (if i.val < 1331 then 10 else (if i.val < 1332 then 60 else 49))))) else (if i.val < 1341 then (if i.val < 1337 then (if i.val < 1335 then (if i.val < 1334 then 16 else 57) else (if i.val < 1336 then 21 else 46)) else (if i.val < 1339 then (if i.val < 1338 then 49 else 60) else (if i.val < 1340 then 34 else 21))) else (if i.val < 1345 then (if i.val < 1343 then (if i.val < 1342 then 86 else 4) else (if i.val < 1344 then 71 else 47)) else (if i.val < 1347 then (if i.val < 1346 then 22 else 46) else (if i.val < 1348 then 49 else (if i.val < 1349 then 57 else 86))))))))) else (if i.val < 1485 then (if i.val < 1417 then (if i.val < 1383 then (if i.val < 1366 then (if i.val < 1358 then (if i.val < 1354 then (if i.val < 1352 then (if i.val < 1351 then 16 else 46) else (if i.val < 1353 then 60 else 57)) else (if i.val < 1356 then (if i.val < 1355 then 21 else 60) else (if i.val < 1357 then 49 else 57))) else (if i.val < 1362 then (if i.val < 1360 then (if i.val < 1359 then 57 else 38) else (if i.val < 1361 then 46 else 35)) else (if i.val < 1364 then (if i.val < 1363 then 34 else 38) else (if i.val < 1365 then 34 else 40)))) else (if i.val < 1374 then (if i.val < 1370 then (if i.val < 1368 then (if i.val < 1367 then 86 else 16) else (if i.val < 1369 then 57 else 21)) else (if i.val < 1372 then (if i.val < 1371 then 10 else 60) else (if i.val < 1373 then 57 else 21))) else (if i.val < 1378 then (if i.val < 1376 then (if i.val < 1375 then 49 else 57) else (if i.val < 1377 then 69 else 69)) else (if i.val < 1380 then (if i.val < 1379 then 46 else 22) else (if i.val < 1381 then 86 else (if i.val < 1382 then 4 else 49)))))) else (if i.val < 1400 then (if i.val < 1391 then (if i.val < 1387 then (if i.val < 1385 then (if i.val < 1384 then 60 else 21) else (if i.val < 1386 then 10 else 38)) else (if i.val < 1389 then (if i.val < 1388 then 49 else 60) else (if i.val < 1390 then 86 else 16))) else (if i.val < 1395 then (if i.val < 1393 then (if i.val < 1392 then 21 else 86) else (if i.val < 1394 then 46 else 57)) else (if i.val < 1397 then (if i.val < 1396 then 46 else 16) else (if i.val < 1398 then 32 else (if i.val < 1399 then 71 else 10))))) else (if i.val < 1408 then (if i.val < 1404 then (if i.val < 1402 then (if i.val < 1401 then 57 else 92) else (if i.val < 1403 then 40 else 49)) else (if i.val < 1406 then (if i.val < 1405 then 73 else 13) else (if i.val < 1407 then 46 else 16))) else (if i.val < 1412 then (if i.val < 1410 then (if i.val < 1409 then 38 else 10) else (if i.val < 1411 then 35 else 60)) else (if i.val < 1414 then (if i.val < 1413 then 21 else 49) else (if i.val < 1415 then 60 else (if i.val < 1416 then 57 else 38))))))) else (if i.val < 1451 then (if i.val < 1434 then (if i.val < 1425 then (if i.val < 1421 then (if i.val < 1419 then (if i.val < 1418 then 49 else 16) else (if i.val < 1420 then 46 else 16)) else (if i.val < 1423 then (if i.val < 1422 then 49 else 57) else (if i.val < 1424 then 60 else 38))) else (if i.val < 1429 then (if i.val < 1427 then (if i.val < 1426 then 34 else 18) else (if i.val < 1428 then 47 else 16)) else (if i.val < 1431 then (if i.val < 1430 then 4 else 71) else (if i.val < 1432 then 71 else (if i.val < 1433 then 56 else 15))))) else (if i.val < 1442 then (if i.val < 1438 then (if i.val < 1436 then (if i.val < 1435 then 22 else 86) else (if i.val < 1437 then 46 else 49)) else (if i.val < 1440 then (if i.val < 1439 then 60 else 21) else (if i.val < 1441 then 46 else 86))) else (if i.val < 1446 then (if i.val < 1444 then (if i.val < 1443 then 34 else 71) else (if i.val < 1445 then 46 else 57)) else (if i.val < 1448 then (if i.val < 1447 then 60 else 38) else (if i.val < 1449 then 57 else (if i.val < 1450 then 40 else 49)))))) else (if i.val < 1468 then (if i.val < 1459 then (if i.val < 1455 then (if i.val < 1453 then (if i.val < 1452 then 46 else 60) else (if i.val < 1454 then 40 else 49)) else (if i.val < 1457 then (if i.val < 1456 then 16 else 21) else (if i.val < 1458 then 57 else 38))) else (if i.val < 1463 then (if i.val < 1461 then (if i.val < 1460 then 38 else 26) else (if i.val < 1462 then 32 else 35)) else (if i.val < 1465 then (if i.val < 1464 then 38 else 34) else (if i.val < 1466 then 21 else (if i.val < 1467 then 38 else 47))))) else (if i.val < 1476 then (if i.val < 1472 then (if i.val < 1470 then (if i.val < 1469 then 40 else 30) else (if i.val < 1471 then 49 else 60)) else (if i.val < 1474 then (if i.val < 1473 then 57 else 21) else (if i.val < 1475 then 86 else 16))) else (if i.val < 1480 then (if i.val < 1478 then (if i.val < 1477 then 71 else 57) else (if i.val < 1479 then 40 else 21)) else (if i.val < 1482 then (if i.val < 1481 then 49 else 92) else (if i.val < 1483 then 40 else (if i.val < 1484 then 57 else 21)))))))) else (if i.val < 1552 then (if i.val < 1518 then (if i.val < 1501 then (if i.val < 1493 then (if i.val < 1489 then (if i.val < 1487 then (if i.val < 1486 then 13 else 34) else (if i.val < 1488 then 40 else 21)) else (if i.val < 1491 then (if i.val < 1490 then 26 else 21) else (if i.val < 1492 then 11 else 66))) else (if i.val < 1497 then (if i.val < 1495 then (if i.val < 1494 then 38 else 69) else (if i.val < 1496 then 46 else 69)) else (if i.val < 1499 then (if i.val < 1498 then 10 else 46) else (if i.val < 1500 then 92 else 22)))) else (if i.val < 1509 then (if i.val < 1505 then (if i.val < 1503 then (if i.val < 1502 then 13 else 16) else (if i.val < 1504 then 4 else 21)) else (if i.val < 1507 then (if i.val < 1506 then 46 else 60) else (if i.val < 1508 then 57 else 35))) else (if i.val < 1513 then (if i.val < 1511 then (if i.val < 1510 then 40 else 16) else (if i.val < 1512 then 60 else 26)) else (if i.val < 1515 then (if i.val < 1514 then 69 else 86) else (if i.val < 1516 then 60 else (if i.val < 1517 then 13 else 49)))))) else (if i.val < 1535 then (if i.val < 1526 then (if i.val < 1522 then (if i.val < 1520 then (if i.val < 1519 then 60 else 86) else (if i.val < 1521 then 32 else 16)) else (if i.val < 1524 then (if i.val < 1523 then 38 else 49) else (if i.val < 1525 then 86 else 60))) else (if i.val < 1530 then (if i.val < 1528 then (if i.val < 1527 then 46 else 34) else (if i.val < 1529 then 57 else 40)) else (if i.val < 1532 then (if i.val < 1531 then 35 else 16) else (if i.val < 1533 then 38 else (if i.val < 1534 then 32 else 21))))) else (if i.val < 1543 then (if i.val < 1539 then (if i.val < 1537 then (if i.val < 1536 then 71 else 49) else (if i.val < 1538 then 60 else 57)) else (if i.val < 1541 then (if i.val < 1540 then 40 else 92) else (if i.val < 1542 then 21 else 40))) else (if i.val < 1547 then (if i.val < 1545 then (if i.val < 1544 then 11 else 66) else (if i.val < 1546 then 73 else 10)) else (if i.val < 1549 then (if i.val < 1548 then 60 else 46) else (if i.val < 1550 then 57 else (if i.val < 1551 then 16 else 21))))))) else (if i.val < 1586 then (if i.val < 1569 then (if i.val < 1560 then (if i.val < 1556 then (if i.val < 1554 then (if i.val < 1553 then 86 else 57) else (if i.val < 1555 then 32 else 38)) else (if i.val < 1558 then (if i.val < 1557 then 10 else 34) else (if i.val < 1559 then 35 else 21))) else (if i.val < 1564 then (if i.val < 1562 then (if i.val < 1561 then 60 else 21) else (if i.val < 1563 then 49 else 57)) else (if i.val < 1566 then (if i.val < 1565 then 60 else 21) else (if i.val < 1567 then 57 else (if i.val < 1568 then 21 else 47))))) else (if i.val < 1577 then (if i.val < 1573 then (if i.val < 1571 then (if i.val < 1570 then 57 else 46) else (if i.val < 1572 then 57 else 16)) else (if i.val < 1575 then (if i.val < 1574 then 38 else 32) else (if i.val < 1576 then 38 else 16))) else (if i.val < 1581 then (if i.val < 1579 then (if i.val < 1578 then 21 else 16) else (if i.val < 1580 then 38 else 60)) else (if i.val < 1583 then (if i.val < 1582 then 21 else 49) else (if i.val < 1584 then 21 else (if i.val < 1585 then 18 else 57)))))) else (if i.val < 1603 then (if i.val < 1594 then (if i.val < 1590 then (if i.val < 1588 then (if i.val < 1587 then 16 else 38) else (if i.val < 1589 then 4 else 21)) else (if i.val < 1592 then (if i.val < 1591 then 71 else 13) else (if i.val < 1593 then 71 else 47))) else (if i.val < 1598 then (if i.val < 1596 then (if i.val < 1595 then 56 else 15) else (if i.val < 1597 then 38 else 46)) else (if i.val < 1600 then (if i.val < 1599 then 86 else 32) else (if i.val < 1601 then 46 else (if i.val < 1602 then 57 else 71))))) else (if i.val < 1611 then (if i.val < 1607 then (if i.val < 1605 then (if i.val < 1604 then 49 else 16) else (if i.val < 1606 then 60 else 38)) else (if i.val < 1609 then (if i.val < 1608 then 57 else 47) else (if i.val < 1610 then 46 else 35))) else (if i.val < 1615 then (if i.val < 1613 then (if i.val < 1612 then 86 else 16) else (if i.val < 1614 then 71 else 49)) else (if i.val < 1617 then (if i.val < 1616 then 16 else 57) else (if i.val < 1618 then 60 else (if i.val < 1619 then 21 else 38)))))))))) else (if i.val < 1890 then (if i.val < 1755 then (if i.val < 1687 then (if i.val < 1653 then (if i.val < 1636 then (if i.val < 1628 then (if i.val < 1624 then (if i.val < 1622 then (if i.val < 1621 then 49 else 57) else (if i.val < 1623 then 71 else 40)) else (if i.val < 1626 then (if i.val < 1625 then 46 else 60) else (if i.val < 1627 then 10 else 18))) else (if i.val < 1632 then (if i.val < 1630 then (if i.val < 1629 then 38 else 40) else (if i.val < 1631 then 26 else 60)) else (if i.val < 1634 then (if i.val < 1633 then 16 else 21) else (if i.val < 1635 then 47 else 57)))) else (if i.val < 1644 then (if i.val < 1640 then (if i.val < 1638 then (if i.val < 1637 then 38 else 38) else (if i.val < 1639 then 49 else 57)) else (if i.val < 1642 then (if i.val < 1641 then 32 else 38) else (if i.val < 1643 then 35 else 21))) else (if i.val < 1648 then (if i.val < 1646 then (if i.val < 1645 then 38 else 26) else (if i.val < 1647 then 34 else 18)) else (if i.val < 1650 then (if i.val < 1649 then 21 else 13) else (if i.val < 1651 then 38 else (if i.val < 1652 then 13 else 30)))))) else (if i.val < 1670 then (if i.val < 1661 then (if i.val < 1657 then (if i.val < 1655 then (if i.val < 1654 then 40 else 49) else (if i.val < 1656 then 16 else 60)) else (if i.val < 1659 then (if i.val < 1658 then 21 else 49) else (if i.val < 1660 then 4 else 16))) else (if i.val < 1665 then (if i.val < 1663 then (if i.val < 1662 then 21 else 71) else (if i.val < 1664 then 57 else 71)) else (if i.val < 1667 then (if i.val < 1666 then 47 else 13) else (if i.val < 1668 then 92 else (if i.val < 1669 then 40 else 40))))) else (if i.val < 1678 then (if i.val < 1674 then (if i.val < 1672 then (if i.val < 1671 then 11 else 57) else (if i.val < 1673 then 38 else 26)) else (if i.val < 1676 then (if i.val < 1675 then 49 else 13) else (if i.val < 1677 then 66 else 71))) else (if i.val < 1682 then (if i.val < 1680 then (if i.val < 1679 then 40 else 49) else (if i.val < 1681 then 26 else 21)) else (if i.val < 1684 then (if i.val < 1683 then 11 else 46) else (if i.val < 1685 then 57 else (if i.val < 1686 then 10 else 16))))))) else (if i.val < 1721 then (if i.val < 1704 then (if i.val < 1695 then (if i.val < 1691 then (if i.val < 1689 then (if i.val < 1688 then 46 else 92) else (if i.val < 1690 then 21 else 46)) else (if i.val < 1693 then (if i.val < 1692 then 13 else 60) else (if i.val < 1694 then 16 else 21))) else (if i.val < 1699 then (if i.val < 1697 then (if i.val < 1696 then 4 else 71) else (if i.val < 1698 then 47 else 46)) else (if i.val < 1701 then (if i.val < 1700 then 57 else 10) else (if i.val < 1702 then 16 else (if i.val < 1703 then 60 else 21))))) else (if i.val < 1712 then (if i.val < 1708 then (if i.val < 1706 then (if i.val < 1705 then 60 else 57) else (if i.val < 1707 then 38 else 35)) else (if i.val < 1710 then (if i.val < 1709 then 38 else 40) else (if i.val < 1711 then 26 else 16))) else (if i.val < 1716 then (if i.val < 1714 then (if i.val < 1713 then 60 else 38) else (if i.val < 1715 then 57 else 69)) else (if i.val < 1718 then (if i.val < 1717 then 46 else 86) else (if i.val < 1719 then 4 else (if i.val < 1720 then 60 else 16)))))) else (if i.val < 1738 then (if i.val < 1729 then (if i.val < 1725 then (if i.val < 1723 then (if i.val < 1722 then 49 else 60) else (if i.val < 1724 then 21 else 49)) else (if i.val < 1727 then (if i.val < 1726 then 16 else 32) else (if i.val < 1728 then 71 else 71))) else (if i.val < 1733 then (if i.val < 1731 then (if i.val < 1730 then 56 else 15) else (if i.val < 1732 then 86 else 16)) else (if i.val < 1735 then (if i.val < 1734 then 60 else 21) else (if i.val < 1736 then 46 else (if i.val < 1737 then 34 else 71))))) else (if i.val < 1746 then (if i.val < 1742 then (if i.val < 1740 then (if i.val < 1739 then 38 else 40) else (if i.val < 1741 then 49 else 40)) else (if i.val < 1744 then (if i.val < 1743 then 16 else 21) else (if i.val < 1745 then 38 else 26))) else (if i.val < 1750 then (if i.val < 1748 then (if i.val < 1747 then 32 else 38) else (if i.val < 1749 then 21 else 47)) else (if i.val < 1752 then (if i.val < 1751 then 71 else 49) else (if i.val < 1753 then 30 else (if i.val < 1754 then 60 else 21)))))))) else (if i.val < 1822 then (if i.val < 1788 then (if i.val < 1771 then (if i.val < 1763 then (if i.val < 1759 then (if i.val < 1757 then (if i.val < 1756 then 71 else 40) else (if i.val < 1758 then 49 else 92)) else (if i.val < 1761 then (if i.val < 1760 then 40 else 21) else (if i.val < 1762 then 40 else 11))) else (if i.val < 1767 then (if i.val < 1765 then (if i.val < 1764 then 66 else 38) else (if i.val < 1766 then 46 else 10)) else (if i.val < 1769 then (if i.val < 1768 then 92 else 13) else (if i.val < 1770 then 16 else 21)))) else (if i.val < 1779 then (if i.val < 1775 then (if i.val < 1773 then (if i.val < 1772 then 46 else 60) else (if i.val < 1774 then 57 else 40)) else (if i.val < 1777 then (if i.val < 1776 then 16 else 21) else (if i.val < 1778 then 26 else 86))) else (if i.val < 1783 then (if i.val < 1781 then (if i.val < 1780 then 38 else 32) else (if i.val < 1782 then 38 else 49)) else (if i.val < 1785 then (if i.val < 1784 then 60 else 34) else (if i.val < 1786 then 40 else (if i.val < 1787 then 38 else 21)))))) else (if i.val < 1805 then (if i.val < 1796 then (if i.val < 1792 then (if i.val < 1790 then (if i.val < 1789 then 49 else 60) else (if i.val < 1791 then 40 else 21)) else (if i.val < 1794 then (if i.val < 1793 then 11 else 66) else (if i.val < 1795 then 10 else 60))) else (if i.val < 1800 then (if i.val < 1798 then (if i.val < 1797 then 57 else 21) else (if i.val < 1799 then 86 else 38)) else (if i.val < 1802 then (if i.val < 1801 then 34 else 21) else (if i.val < 1803 then 21 else (if i.val < 1804 then 49 else 21))))) else (if i.val < 1813 then (if i.val < 1809 then (if i.val < 1807 then (if i.val < 1806 then 21 else 47) else (if i.val < 1808 then 57 else 57)) else (if i.val < 1811 then (if i.val < 1810 then 38 else 60) else (if i.val < 1812 then 38 else 38))) else (if i.val < 1817 then (if i.val < 1815 then (if i.val < 1814 then 21 else 13) else (if i.val < 1816 then 47 else 15)) else (if i.val < 1819 then (if i.val < 1818 then 38 else 46) else (if i.val < 1820 then 32 else (if i.val < 1821 then 57 else 71))))))) else (if i.val < 1856 then (if i.val < 1839 then (if i.val < 1830 then (if i.val < 1826 then (if i.val < 1824 then (if i.val < 1823 then 16 else 38) else (if i.val < 1825 then 38 else 47)) else (if i.val < 1828 then (if i.val < 1827 then 32 else 21) else (if i.val < 1829 then 49 else 16))) else (if i.val < 1834 then (if i.val < 1832 then (if i.val < 1831 then 38 else 21) else (if i.val < 1833 then 49 else 30)) else (if i.val < 1836 then (if i.val < 1835 then 21 else 18) else (if i.val < 1837 then 38 else (if i.val < 1838 then 26 else 21))))) else (if i.val < 1847 then (if i.val < 1843 then (if i.val < 1841 then (if i.val < 1840 then 47 else 38) else (if i.val < 1842 then 13 else 49)) else (if i.val < 1845 then (if i.val < 1844 then 57 else 38) else (if i.val < 1846 then 26 else 13))) else (if i.val < 1851 then (if i.val < 1849 then (if i.val < 1848 then 69 else 16) else (if i.val < 1850 then 21 else 38)) else (if i.val < 1853 then (if i.val < 1852 then 49 else 4) else (if i.val < 1854 then 56 else (if i.val < 1855 then 71 else 47)))))) else (if i.val < 1873 then (if i.val < 1864 then (if i.val < 1860 then (if i.val < 1858 then (if i.val < 1857 then 13 else 15) else (if i.val < 1859 then 40 else 11)) else (if i.val < 1862 then (if i.val < 1861 then 71 else 49) else (if i.val < 1863 then 47 else 30))) else (if i.val < 1868 then (if i.val < 1866 then (if i.val < 1865 then 69 else 46) else (if i.val < 1867 then 57 else 86)) else (if i.val < 1870 then (if i.val < 1869 then 32 else 21) else (if i.val < 1871 then 46 else (if i.val < 1872 then 60 else 71))))) else (if i.val < 1881 then (if i.val < 1877 then (if i.val < 1875 then (if i.val < 1874 then 47 else 57) else (if i.val < 1876 then 16 else 21)) else (if i.val < 1879 then (if i.val < 1878 then 60 else 38) else (if i.val < 1880 then 38 else 21))) else (if i.val < 1885 then (if i.val < 1883 then (if i.val < 1882 then 57 else 46) else (if i.val < 1884 then 4 else 21)) else (if i.val < 1887 then (if i.val < 1886 then 16 else 16) else (if i.val < 1888 then 71 else (if i.val < 1889 then 71 else 56))))))))) else (if i.val < 2025 then (if i.val < 1957 then (if i.val < 1923 then (if i.val < 1906 then (if i.val < 1898 then (if i.val < 1894 then (if i.val < 1892 then (if i.val < 1891 then 15 else 16) else (if i.val < 1893 then 21 else 71)) else (if i.val < 1896 then (if i.val < 1895 then 40 else 21) else (if i.val < 1897 then 26 else 49))) else (if i.val < 1902 then (if i.val < 1900 then (if i.val < 1899 then 21 else 71) else (if i.val < 1901 then 49 else 40)) else (if i.val < 1904 then (if i.val < 1903 then 13 else 26) else (if i.val < 1905 then 66 else 92)))) else (if i.val < 1914 then (if i.val < 1910 then (if i.val < 1908 then (if i.val < 1907 then 16 else 21) else (if i.val < 1909 then 40 else 60)) else (if i.val < 1912 then (if i.val < 1911 then 49 else 60) else (if i.val < 1913 then 40 else 38))) else (if i.val < 1918 then (if i.val < 1916 then (if i.val < 1915 then 49 else 40) else (if i.val < 1917 then 66 else 60)) else (if i.val < 1920 then (if i.val < 1919 then 21 else 16) else (if i.val < 1921 then 38 else (if i.val < 1922 then 21 else 49)))))) else (if i.val < 1940 then (if i.val < 1931 then (if i.val < 1927 then (if i.val < 1925 then (if i.val < 1924 then 21 else 26) else (if i.val < 1926 then 47 else 57)) else (if i.val < 1929 then (if i.val < 1928 then 38 else 38) else (if i.val < 1930 then 47 else 38))) else (if i.val < 1935 then (if i.val < 1933 then (if i.val < 1932 then 13 else 15) else (if i.val < 1934 then 38 else 32)) else (if i.val < 1937 then (if i.val < 1936 then 71 else 38) else (if i.val < 1938 then 47 else (if i.val < 1939 then 49 else 49))))) else (if i.val < 1948 then (if i.val < 1944 then (if i.val < 1942 then (if i.val < 1941 then 30 else 21) else (if i.val < 1943 then 18 else 26)) else (if i.val < 1946 then (if i.val < 1945 then 47 else 13) else (if i.val < 1947 then 57 else 38))) else (if i.val < 1952 then (if i.val < 1950 then (if i.val < 1949 then 26 else 13) else (if i.val < 1951 then 69 else 49)) else (if i.val < 1954 then (if i.val < 1953 then 40 else 11) else (if i.val < 1955 then 57 else (if i.val < 1956 then 16 else 21))))))) else (if i.val < 1991 then (if i.val < 1974 then (if i.val < 1965 then (if i.val < 1961 then (if i.val < 1959 then (if i.val < 1958 then 60 else 21) else (if i.val < 1960 then 47 else 21)) else (if i.val < 1963 then (if i.val < 1962 then 49 else 57) else (if i.val < 1964 then 4 else 21))) else (if i.val < 1969 then (if i.val < 1967 then (if i.val < 1966 then 16 else 71) else (if i.val < 1968 then 56 else 15)) else (if i.val < 1971 then (if i.val < 1970 then 21 else 71) else (if i.val < 1972 then 40 else (if i.val < 1973 then 26 else 47))))) else (if i.val < 1982 then (if i.val < 1978 then (if i.val < 1976 then (if i.val < 1975 then 13 else 66) else (if i.val < 1977 then 92 else 21)) else (if i.val < 1980 then (if i.val < 1979 then 40 else 40) else (if i.val < 1981 then 49 else 11))) else (if i.val < 1986 then (if i.val < 1984 then (if i.val < 1983 then 66 else 21) else (if i.val < 1985 then 38 else 49)) else (if i.val < 1988 then (if i.val < 1987 then 26 else 57) else (if i.val < 1989 then 13 else (if i.val < 1990 then 15 else 38)))))) else (if i.val < 2008 then (if i.val < 1999 then (if i.val < 1995 then (if i.val < 1993 then (if i.val < 1992 then 71 else 47) else (if i.val < 1994 then 40 else 49)) else (if i.val < 1997 then (if i.val < 1996 then 49 else 26) else (if i.val < 1998 then 47 else 57))) else (if i.val < 2003 then (if i.val < 2001 then (if i.val < 2000 then 26 else 30) else (if i.val < 2002 then 49 else 11)) else (if i.val < 2005 then (if i.val < 2004 then 46 else 92) else (if i.val < 2006 then 34 else (if i.val < 2007 then 47 else 92))))) else (if i.val < 2016 then (if i.val < 2012 then (if i.val < 2010 then (if i.val < 2009 then 32 else 92) else (if i.val < 2011 then 40 else 38)) else (if i.val < 2014 then (if i.val < 2013 then 84 else 34) else (if i.val < 2015 then 40 else 47))) else (if i.val < 2020 then (if i.val < 2018 then (if i.val < 2017 then 66 else 38) else (if i.val < 2019 then 38 else 56)) else (if i.val < 2022 then (if i.val < 2021 then 40 else 26) else (if i.val < 2023 then 26 else (if i.val < 2024 then 84 else 57)))))))) else (if i.val < 2092 then (if i.val < 2058 then (if i.val < 2041 then (if i.val < 2033 then (if i.val < 2029 then (if i.val < 2027 then (if i.val < 2026 then 24 else 71) else (if i.val < 2028 then 92 else 40)) else (if i.val < 2031 then (if i.val < 2030 then 11 else 84) else (if i.val < 2032 then 66 else 71))) else (if i.val < 2037 then (if i.val < 2035 then (if i.val < 2034 then 40 else 26) else (if i.val < 2036 then 47 else 69)) else (if i.val < 2039 then (if i.val < 2038 then 26 else 38) else (if i.val < 2040 then 26 else 56)))) else (if i.val < 2049 then (if i.val < 2045 then (if i.val < 2043 then (if i.val < 2042 then 57 else 11) else (if i.val < 2044 then 66 else 26)) else (if i.val < 2047 then (if i.val < 2046 then 66 else 84) else (if i.val < 2048 then 57 else 47))) else (if i.val < 2053 then (if i.val < 2051 then (if i.val < 2050 then 15 else 75) else (if i.val < 2052 then 86 else 71)) else (if i.val < 2055 then (if i.val < 2054 then 47 else 38) else (if i.val < 2056 then 40 else (if i.val < 2057 then 66 else 56)))))) else (if i.val < 2075 then (if i.val < 2066 then (if i.val < 2062 then (if i.val < 2060 then (if i.val < 2059 then 84 else 57) else (if i.val < 2061 then 24 else 71)) else (if i.val < 2064 then (if i.val < 2063 then 47 else 40) else (if i.val < 2065 then 26 else 66))) else (if i.val < 2070 then (if i.val < 2068 then (if i.val < 2067 then 15 else 69) else (if i.val < 2069 then 26 else 11)) else (if i.val < 2072 then (if i.val < 2071 then 66 else 66) else (if i.val < 2073 then 57 else (if i.val < 2074 then 75 else 86))))) else (if i.val < 2083 then (if i.val < 2079 then (if i.val < 2077 then (if i.val < 2076 then 47 else 26) else (if i.val < 2078 then 66 else 56)) else (if i.val < 2081 then (if i.val < 2080 then 57 else 24) else (if i.val < 2082 then 66 else 69))) else (if i.val < 2087 then (if i.val < 2085 then (if i.val < 2084 then 26 else 66) else (if i.val < 2086 then 24 else 57)) else (if i.val < 2089 then (if i.val < 2088 then 75 else 84) else (if i.val < 2090 then 66 else (if i.val < 2091 then 57 else 24))))))) else (if i.val < 2126 then (if i.val < 2109 then (if i.val < 2100 then (if i.val < 2096 then (if i.val < 2094 then (if i.val < 2093 then 66 else 75) else (if i.val < 2095 then 86 else 37)) else (if i.val < 2098 then (if i.val < 2097 then 71 else 45) else (if i.val < 2099 then 15 else 47))) else (if i.val < 2104 then (if i.val < 2102 then (if i.val < 2101 then 15 else 75) else (if i.val < 2103 then 13 else 40)) else (if i.val < 2106 then (if i.val < 2105 then 26 else 66) else (if i.val < 2107 then 11 else (if i.val < 2108 then 66 else 24))))) else (if i.val < 2117 then (if i.val < 2113 then (if i.val < 2111 then (if i.val < 2110 then 56 else 15) else (if i.val < 2112 then 84 else 34)) else (if i.val < 2115 then (if i.val < 2114 then 49 else 71) else (if i.val < 2116 then 13 else 47))) else (if i.val < 2121 then (if i.val < 2119 then (if i.val < 2118 then 15 else 40) else (if i.val < 2120 then 26 else 66)) else (if i.val < 2123 then (if i.val < 2122 then 69 else 26) else (if i.val < 2124 then 57 else (if i.val < 2125 then 10 else 30)))))) else (if i.val < 2143 then (if i.val < 2134 then (if i.val < 2130 then (if i.val < 2128 then (if i.val < 2127 then 11 else 66) else (if i.val < 2129 then 22 else 66)) else (if i.val < 2132 then (if i.val < 2131 then 38 else 86) else (if i.val < 2133 then 15 else 57))) else (if i.val < 2138 then (if i.val < 2136 then (if i.val < 2135 then 73 else 75) else (if i.val < 2137 then 60 else 38)) else (if i.val < 2140 then (if i.val < 2139 then 13 else 47) else (if i.val < 2141 then 26 else (if i.val < 2142 then 30 else 24))))) else (if i.val < 2151 then (if i.val < 2147 then (if i.val < 2145 then (if i.val < 2144 then 26 else 57) else (if i.val < 2146 then 38 else 15)) else (if i.val < 2149 then (if i.val < 2148 then 57 else 73) else (if i.val < 2150 then 57 else 73))) else (if i.val < 2155 then (if i.val < 2153 then (if i.val < 2152 then 49 else 66) else (if i.val < 2154 then 22 else 26)) else (if i.val < 2157 then (if i.val < 2156 then 66 else 6) else (if i.val < 2158 then 66 else (if i.val < 2159 then 22 else 57)))))))))))) else (if i.val < 3240 then (if i.val < 2700 then (if i.val < 2430 then (if i.val < 2295 then (if i.val < 2227 then (if i.val < 2193 then (if i.val < 2176 then (if i.val < 2168 then (if i.val < 2164 then (if i.val < 2162 then (if i.val < 2161 then 57 else 73) else (if i.val < 2163 then 66 else 24)) else (if i.val < 2166 then (if i.val < 2165 then 46 else 75) else (if i.val < 2167 then 84 else 66))) else (if i.val < 2172 then (if i.val < 2170 then (if i.val < 2169 then 22 else 57) else (if i.val < 2171 then 38 else 24)) else (if i.val < 2174 then (if i.val < 2173 then 86 else 15) else (if i.val < 2175 then 38 else 15)))) else (if i.val < 2184 then (if i.val < 2180 then (if i.val < 2178 then (if i.val < 2177 then 78 else 75) else (if i.val < 2179 then 10 else 60)) else (if i.val < 2182 then (if i.val < 2181 then 71 else 49) else (if i.val < 2183 then 38 else 26))) else (if i.val < 2188 then (if i.val < 2186 then (if i.val < 2185 then 34 else 71) else (if i.val < 2187 then 47 else 57)) else (if i.val < 2190 then (if i.val < 2189 then 75 else 57) else (if i.val < 2191 then 15 else (if i.val < 2192 then 49 else 57)))))) else (if i.val < 2210 then (if i.val < 2201 then (if i.val < 2197 then (if i.val < 2195 then (if i.val < 2194 then 47 else 26) else (if i.val < 2196 then 66 else 11)) else (if i.val < 2199 then (if i.val < 2198 then 66 else 66) else (if i.val < 2200 then 69 else 86))) else (if i.val < 2205 then (if i.val < 2203 then (if i.val < 2202 then 34 else 56) else (if i.val < 2204 then 57 else 15)) else (if i.val < 2207 then (if i.val < 2206 then 75 else 66) else (if i.val < 2208 then 57 else (if i.val < 2209 then 6 else 22))))) else (if i.val < 2218 then (if i.val < 2214 then (if i.val < 2212 then (if i.val < 2211 then 73 else 49) else (if i.val < 2213 then 57 else 34)) else (if i.val < 2216 then (if i.val < 2215 then 75 else 38) else (if i.val < 2217 then 38 else 13))) else (if i.val < 2222 then (if i.val < 2220 then (if i.val < 2219 then 32 else 71) else (if i.val < 2221 then 47 else 65)) else (if i.val < 2224 then (if i.val < 2223 then 30 else 15) else (if i.val < 2225 then 69 else (if i.val < 2226 then 26 else 26))))))) else (if i.val < 2261 then (if i.val < 2244 then (if i.val < 2235 then (if i.val < 2231 then (if i.val < 2229 then (if i.val < 2228 then 57 else 65) else (if i.val < 2230 then 22 else 66)) else (if i.val < 2233 then (if i.val < 2232 then 22 else 86) else (if i.val < 2234 then 66 else 57))) else (if i.val < 2239 then (if i.val < 2237 then (if i.val < 2236 then 15 else 38) else (if i.val < 2238 then 46 else 30)) else (if i.val < 2241 then (if i.val < 2240 then 22 else 57) else (if i.val < 2242 then 69 else (if i.val < 2243 then 66 else 69))))) else (if i.val < 2252 then (if i.val < 2248 then (if i.val < 2246 then (if i.val < 2245 then 46 else 22) else (if i.val < 2247 then 38 else 15)) else (if i.val < 2250 then (if i.val < 2249 then 38 else 22) else (if i.val < 2251 then 73 else 49))) else (if i.val < 2256 then (if i.val < 2254 then (if i.val < 2253 then 75 else 46) else (if i.val < 2255 then 10 else 60)) else (if i.val < 2258 then (if i.val < 2257 then 71 else 49) else (if i.val < 2259 then 13 else (if i.val < 2260 then 15 else 57)))))) else (if i.val < 2278 then (if i.val < 2269 then (if i.val < 2265 then (if i.val < 2263 then (if i.val < 2262 then 26 else 34) else (if i.val < 2264 then 30 else 73)) else (if i.val < 2267 then (if i.val < 2266 then 49 else 49) else (if i.val < 2268 then 15 else 38))) else (if i.val < 2273 then (if i.val < 2271 then (if i.val < 2270 then 49 else 15) else (if i.val < 2272 then 15 else 57)) else (if i.val < 2275 then (if i.val < 2274 then 22 else 73) else (if i.val < 2276 then 10 else (if i.val < 2277 then 57 else 75))))) else (if i.val < 2286 then (if i.val < 2282 then (if i.val < 2280 then (if i.val < 2279 then 73 else 47) else (if i.val < 2281 then 24 else 22)) else (if i.val < 2284 then (if i.val < 2283 then 86 else 57) else (if i.val < 2285 then 66 else 6))) else (if i.val < 2290 then (if i.val < 2288 then (if i.val < 2287 then 49 else 66) else (if i.val < 2289 then 6 else 69)) else (if i.val < 2292 then (if i.val < 2291 then 46 else 16) else (if i.val < 2293 then 57 else (if i.val < 2294 then 73 else 73)))))))) else (if i.val < 2362 then (if i.val < 2328 then (if i.val < 2311 then (if i.val < 2303 then (if i.val < 2299 then (if i.val < 2297 then (if i.val < 2296 then 13 else 66) else (if i.val < 2298 then 22 else 46)) else (if i.val < 2301 then (if i.val < 2300 then 24 else 16) else (if i.val < 2302 then 75 else 47))) else (if i.val < 2307 then (if i.val < 2305 then (if i.val < 2304 then 57 else 69) else (if i.val < 2306 then 86 else 34)) else (if i.val < 2309 then (if i.val < 2308 then 66 else 6) else (if i.val < 2310 then 22 else 57)))) else (if i.val < 2319 then (if i.val < 2315 then (if i.val < 2313 then (if i.val < 2312 then 75 else 13) else (if i.val < 2314 then 49 else 15)) else (if i.val < 2317 then (if i.val < 2316 then 73 else 38) else (if i.val < 2318 then 49 else 15))) else (if i.val < 2323 then (if i.val < 2321 then (if i.val < 2320 then 49 else 10) else (if i.val < 2322 then 60 else 38)) else (if i.val < 2325 then (if i.val < 2324 then 73 else 10) else (if i.val < 2326 then 46 else (if i.val < 2327 then 75 else 10)))))) else (if i.val < 2345 then (if i.val < 2336 then (if i.val < 2332 then (if i.val < 2330 then (if i.val < 2329 then 45 else 15) else (if i.val < 2331 then 26 else 30)) else (if i.val < 2334 then (if i.val < 2333 then 34 else 75) else (if i.val < 2335 then 13 else 47))) else (if i.val < 2340 then (if i.val < 2338 then (if i.val < 2337 then 65 else 57) else (if i.val < 2339 then 73 else 15)) else (if i.val < 2342 then (if i.val < 2341 then 73 else 10) else (if i.val < 2343 then 30 else (if i.val < 2344 then 15 else 66))))) else (if i.val < 2353 then (if i.val < 2349 then (if i.val < 2347 then (if i.val < 2346 then 22 else 57) else (if i.val < 2348 then 38 else 38)) else (if i.val < 2351 then (if i.val < 2350 then 49 else 57) else (if i.val < 2352 then 15 else 78))) else (if i.val < 2357 then (if i.val < 2355 then (if i.val < 2354 then 38 else 26) else (if i.val < 2356 then 47 else 30)) else (if i.val < 2359 then (if i.val < 2358 then 57 else 30) else (if i.val < 2360 then 26 else (if i.val < 2361 then 66 else 24))))))) else (if i.val < 2396 then (if i.val < 2379 then (if i.val < 2370 then (if i.val < 2366 then (if i.val < 2364 then (if i.val < 2363 then 30 else 66) else (if i.val < 2365 then 69 else 22)) else (if i.val < 2368 then (if i.val < 2367 then 46 else 4) else (if i.val < 2369 then 49 else 57))) else (if i.val < 2374 then (if i.val < 2372 then (if i.val < 2371 then 34 else 38) else (if i.val < 2373 then 69 else 22)) else (if i.val < 2376 then (if i.val < 2375 then 75 else 49) else (if i.val < 2377 then 24 else (if i.val < 2378 then 57 else 78))))) else (if i.val < 2387 then (if i.val < 2383 then (if i.val < 2381 then (if i.val < 2380 then 6 else 46) else (if i.val < 2382 then 57 else 22)) else (if i.val < 2385 then (if i.val < 2384 then 86 else 73) else (if i.val < 2386 then 46 else 16))) else (if i.val < 2391 then (if i.val < 2389 then (if i.val < 2388 then 57 else 22) else (if i.val < 2390 then 6 else 75)) else (if i.val < 2393 then (if i.val < 2392 then 49 else 57) else (if i.val < 2394 then 22 else (if i.val < 2395 then 38 else 13)))))) else (if i.val < 2413 then (if i.val < 2404 then (if i.val < 2400 then (if i.val < 2398 then (if i.val < 2397 then 32 else 71) else (if i.val < 2399 then 45 else 47)) else (if i.val < 2402 then (if i.val < 2401 then 57 else 73) else (if i.val < 2403 then 47 else 57))) else (if i.val < 2408 then (if i.val < 2406 then (if i.val < 2405 then 30 else 38) else (if i.val < 2407 then 78 else 10)) else (if i.val < 2410 then (if i.val < 2409 then 26 else 24) else (if i.val < 2411 then 22 else (if i.val < 2412 then 86 else 57))))) else (if i.val < 2421 then (if i.val < 2417 then (if i.val < 2415 then (if i.val < 2414 then 22 else 78) else (if i.val < 2416 then 22 else 46)) else (if i.val < 2419 then (if i.val < 2418 then 66 else 6) else (if i.val < 2420 then 22 else 86))) else (if i.val < 2425 then (if i.val < 2423 then (if i.val < 2422 then 16 else 66) else (if i.val < 2424 then 6 else 57)) else (if i.val < 2427 then (if i.val < 2426 then 78 else 78) else (if i.val < 2428 then 38 else (if i.val < 2429 then 49 else 46))))))))) else (if i.val < 2565 then (if i.val < 2497 then (if i.val < 2463 then (if i.val < 2446 then (if i.val < 2438 then (if i.val < 2434 then (if i.val < 2432 then (if i.val < 2431 then 60 else 40) else (if i.val < 2433 then 26 else 66)) else (if i.val < 2436 then (if i.val < 2435 then 30 else 22) else (if i.val < 2437 then 30 else 6))) else (if i.val < 2442 then (if i.val < 2440 then (if i.val < 2439 then 22 else 65) else (if i.val < 2441 then 78 else 46)) else (if i.val < 2444 then (if i.val < 2443 then 57 else 22) else (if i.val < 2445 then 69 else 46)))) else (if i.val < 2454 then (if i.val < 2450 then (if i.val < 2448 then (if i.val < 2447 then 22 else 69) else (if i.val < 2449 then 46 else 24)) else (if i.val < 2452 then (if i.val < 2451 then 86 else 4) else (if i.val < 2453 then 46 else 15))) else (if i.val < 2458 then (if i.val < 2456 then (if i.val < 2455 then 78 else 10) else (if i.val < 2457 then 73 else 49)) else (if i.val < 2460 then (if i.val < 2459 then 49 else 60) else (if i.val < 2461 then 75 else (if i.val < 2462 then 46 else 46)))))) else (if i.val < 2480 then (if i.val < 2471 then (if i.val < 2467 then (if i.val < 2465 then (if i.val < 2464 then 40 else 13) else (if i.val < 2466 then 57 else 13)) else (if i.val < 2469 then (if i.val < 2468 then 15 else 38) else (if i.val < 2470 then 47 else 30))) else (if i.val < 2475 then (if i.val < 2473 then (if i.val < 2472 then 73 else 49) else (if i.val < 2474 then 30 else 34)) else (if i.val < 2477 then (if i.val < 2476 then 73 else 30) else (if i.val < 2478 then 6 else (if i.val < 2479 then 22 else 16))))) else (if i.val < 2488 then (if i.val < 2484 then (if i.val < 2482 then (if i.val < 2481 then 57 else 65) else (if i.val < 2483 then 66 else 24)) else (if i.val < 2486 then (if i.val < 2485 then 38 else 46) else (if i.val < 2487 then 16 else 15))) else (if i.val < 2492 then (if i.val < 2490 then (if i.val < 2489 then 73 else 22) else (if i.val < 2491 then 69 else 22)) else (if i.val < 2494 then (if i.val < 2493 then 46 else 10) else (if i.val < 2495 then 75 else (if i.val < 2496 then 13 else 73))))))) else (if i.val < 2531 then (if i.val < 2514 then (if i.val < 2505 then (if i.val < 2501 then (if i.val < 2499 then (if i.val < 2498 then 49 else 30) else (if i.val < 2500 then 22 else 30)) else (if i.val < 2503 then (if i.val < 2502 then 46 else 24) else (if i.val < 2504 then 22 else 4))) else (if i.val < 2509 then (if i.val < 2507 then (if i.val < 2506 then 57 else 38) else (if i.val < 2508 then 66 else 24)) else (if i.val < 2511 then (if i.val < 2510 then 6 else 86) else (if i.val < 2512 then 49 else (if i.val < 2513 then 16 else 22))))) else (if i.val < 2522 then (if i.val < 2518 then (if i.val < 2516 then (if i.val < 2515 then 6 else 46) else (if i.val < 2517 then 69 else 46)) else (if i.val < 2520 then (if i.val < 2519 then 57 else 71) else (if i.val < 2521 then 38 else 46))) else (if i.val < 2526 then (if i.val < 2524 then (if i.val < 2523 then 86 else 16) else (if i.val < 2525 then 22 else 86)) else (if i.val < 2528 then (if i.val < 2527 then 10 else 46) else (if i.val < 2529 then 57 else (if i.val < 2530 then 24 else 86)))))) else (if i.val < 2548 then (if i.val < 2539 then (if i.val < 2535 then (if i.val < 2533 then (if i.val < 2532 then 86 else 71) else (if i.val < 2534 then 75 else 46)) else (if i.val < 2537 then (if i.val < 2536 then 57 else 73) else (if i.val < 2538 then 15 else 78))) else (if i.val < 2543 then (if i.val < 2541 then (if i.val < 2540 then 10 else 60) else (if i.val < 2542 then 34 else 38)) else (if i.val < 2545 then (if i.val < 2544 then 66 else 22) else (if i.val < 2546 then 73 else (if i.val < 2547 then 75 else 13))))) else (if i.val < 2556 then (if i.val < 2552 then (if i.val < 2550 then (if i.val < 2549 then 49 else 34) else (if i.val < 2551 then 73 else 73)) else (if i.val < 2554 then (if i.val < 2553 then 38 else 46) else (if i.val < 2555 then 49 else 60))) else (if i.val < 2560 then (if i.val < 2558 then (if i.val < 2557 then 46 else 49) else (if i.val < 2559 then 10 else 35)) else (if i.val < 2562 then (if i.val < 2561 then 38 else 73) else (if i.val < 2563 then 46 else (if i.val < 2564 then 10 else 46)))))))) else (if i.val < 2632 then (if i.val < 2598 then (if i.val < 2581 then (if i.val < 2573 then (if i.val < 2569 then (if i.val < 2567 then (if i.val < 2566 then 10 else 45) else (if i.val < 2568 then 15 else 75)) else (if i.val < 2571 then (if i.val < 2570 then 26 else 66) else (if i.val < 2572 then 30 else 24))) else (if i.val < 2577 then (if i.val < 2575 then (if i.val < 2574 then 15 else 34) else (if i.val < 2576 then 38 else 49)) else (if i.val < 2579 then (if i.val < 2578 then 13 else 15) else (if i.val < 2580 then 47 else 65)))) else (if i.val < 2589 then (if i.val < 2585 then (if i.val < 2583 then (if i.val < 2582 then 69 else 38) else (if i.val < 2584 then 10 else 15)) else (if i.val < 2587 then (if i.val < 2586 then 73 else 60) else (if i.val < 2588 then 13 else 30))) else (if i.val < 2593 then (if i.val < 2591 then (if i.val < 2590 then 30 else 24) else (if i.val < 2592 then 57 else 38)) else (if i.val < 2595 then (if i.val < 2594 then 15 else 73) else (if i.val < 2596 then 49 else (if i.val < 2597 then 22 else 66)))))) else (if i.val < 2615 then (if i.val < 2606 then (if i.val < 2602 then (if i.val < 2600 then (if i.val < 2599 then 6 else 22) else (if i.val < 2601 then 86 else 57)) else (if i.val < 2604 then (if i.val < 2603 then 73 else 38) else (if i.val < 2605 then 46 else 38))) else (if i.val < 2610 then (if i.val < 2608 then (if i.val < 2607 then 22 else 15) else (if i.val < 2609 then 78 else 71)) else (if i.val < 2612 then (if i.val < 2611 then 49 else 26) else (if i.val < 2613 then 34 else (if i.val < 2614 then 47 else 57))))) else (if i.val < 2623 then (if i.val < 2619 then (if i.val < 2617 then (if i.val < 2616 then 57 else 73) else (if i.val < 2618 then 30 else 26)) else (if i.val < 2621 then (if i.val < 2620 then 66 else 22) else (if i.val < 2622 then 16 else 22))) else (if i.val < 2627 then (if i.val < 2625 then (if i.val < 2624 then 66 else 69) else (if i.val < 2626 then 22 else 49)) else (if i.val < 2629 then (if i.val < 2628 then 46 else 60) else (if i.val < 2630 then 49 else (if i.val < 2631 then 15 else 57))))))) else (if i.val < 2666 then (if i.val < 2649 then (if i.val < 2640 then (if i.val < 2636 then (if i.val < 2634 then (if i.val < 2633 then 34 else 49) else (if i.val < 2635 then 15 else 57)) else (if i.val < 2638 then (if i.val < 2637 then 49 else 22) else (if i.val < 2639 then 10 else 10))) else (if i.val < 2644 then (if i.val < 2642 then (if i.val < 2641 then 24 else 86) else (if i.val < 2643 then 57 else 49)) else (if i.val < 2646 then (if i.val < 2645 then 6 else 46) else (if i.val < 2647 then 16 else (if i.val < 2648 then 73 else 13))))) else (if i.val < 2657 then (if i.val < 2653 then (if i.val < 2651 then (if i.val < 2650 then 22 else 46) else (if i.val < 2652 then 86 else 38)) else (if i.val < 2655 then (if i.val < 2654 then 38 else 22) else (if i.val < 2656 then 86 else 6))) else (if i.val < 2661 then (if i.val < 2659 then (if i.val < 2658 then 49 else 13) else (if i.val < 2660 then 49 else 32)) else (if i.val < 2663 then (if i.val < 2662 then 73 else 49) else (if i.val < 2664 then 38 else (if i.val < 2665 then 49 else 10)))))) else (if i.val < 2683 then (if i.val < 2674 then (if i.val < 2670 then (if i.val < 2668 then (if i.val < 2667 then 13 else 57) else (if i.val < 2669 then 45 else 15)) else (if i.val < 2672 then (if i.val < 2671 then 30 else 57) else (if i.val < 2673 then 13 else 65))) else (if i.val < 2678 then (if i.val < 2676 then (if i.val < 2675 then 73 else 73) else (if i.val < 2677 then 10 else 30)) else (if i.val < 2680 then (if i.val < 2679 then 73 else 22) else (if i.val < 2681 then 38 else (if i.val < 2682 then 38 else 78))))) else (if i.val < 2691 then (if i.val < 2687 then (if i.val < 2685 then (if i.val < 2684 then 60 else 26) else (if i.val < 2686 then 30 else 24)) else (if i.val < 2689 then (if i.val < 2688 then 30 else 22) else (if i.val < 2690 then 46 else 4))) else (if i.val < 2695 then (if i.val < 2693 then (if i.val < 2692 then 57 else 38) else (if i.val < 2694 then 57 else 22)) else (if i.val < 2697 then (if i.val < 2696 then 49 else 78) else (if i.val < 2698 then 46 else (if i.val < 2699 then 86 else 46)))))))))) else (if i.val < 2970 then (if i.val < 2835 then (if i.val < 2767 then (if i.val < 2733 then (if i.val < 2716 then (if i.val < 2708 then (if i.val < 2704 then (if i.val < 2702 then (if i.val < 2701 then 16 else 22) else (if i.val < 2703 then 6 else 49)) else (if i.val < 2706 then (if i.val < 2705 then 22 else 46) else (if i.val < 2707 then 86 else 45))) else (if i.val < 2712 then (if i.val < 2710 then (if i.val < 2709 then 57 else 57) else (if i.val < 2711 then 10 else 66)) else (if i.val < 2714 then (if i.val < 2713 then 69 else 86) else (if i.val < 2715 then 57 else 78)))) else (if i.val < 2724 then (if i.val < 2720 then (if i.val < 2718 then (if i.val < 2717 then 46 else 6) else (if i.val < 2719 then 16 else 49)) else (if i.val < 2722 then (if i.val < 2721 then 49 else 60) else (if i.val < 2723 then 40 else 66))) else (if i.val < 2728 then (if i.val < 2726 then (if i.val < 2725 then 22 else 78) else (if i.val < 2727 then 46 else 78)) else (if i.val < 2730 then (if i.val < 2729 then 10 else 46) else (if i.val < 2731 then 49 else (if i.val < 2732 then 60 else 46)))))) else (if i.val < 2750 then (if i.val < 2741 then (if i.val < 2737 then (if i.val < 2735 then (if i.val < 2734 then 60 else 40) else (if i.val < 2736 then 13 else 57)) else (if i.val < 2739 then (if i.val < 2738 then 38 else 30) else (if i.val < 2740 then 49 else 30))) else (if i.val < 2745 then (if i.val < 2743 then (if i.val < 2742 then 73 else 6) else (if i.val < 2744 then 49 else 16)) else (if i.val < 2747 then (if i.val < 2746 then 16 else 46) else (if i.val < 2748 then 46 else (if i.val < 2749 then 92 else 22))))) else (if i.val < 2758 then (if i.val < 2754 then (if i.val < 2752 then (if i.val < 2751 then 46 else 86) else (if i.val < 2753 then 46 else 4)) else (if i.val < 2756 then (if i.val < 2755 then 24 else 86) else (if i.val < 2757 then 16 else 22))) else (if i.val < 2762 then (if i.val < 2760 then (if i.val < 2759 then 46 else 57) else (if i.val < 2761 then 71 else 38)) else (if i.val < 2764 then (if i.val < 2763 then 46 else 16) else (if i.val < 2765 then 10 else (if i.val < 2766 then 57 else 15))))))) else (if i.val < 2801 then (if i.val < 2784 then (if i.val < 2775 then (if i.val < 2771 then (if i.val < 2769 then (if i.val < 2768 then 78 else 10) else (if i.val < 2770 then 60 else 38)) else (if i.val < 2773 then (if i.val < 2772 then 46 else 73) else (if i.val < 2774 then 10 else 57))) else (if i.val < 2779 then (if i.val < 2777 then (if i.val < 2776 then 73 else 10) else (if i.val < 2778 then 46 else 60)) else (if i.val < 2781 then (if i.val < 2780 then 46 else 57) else (if i.val < 2782 then 60 else (if i.val < 2783 then 75 else 15))))) else (if i.val < 2792 then (if i.val < 2788 then (if i.val < 2786 then (if i.val < 2785 then 49 else 15) else (if i.val < 2787 then 30 else 69)) else (if i.val < 2790 then (if i.val < 2789 then 73 else 10) else (if i.val < 2791 then 60 else 30))) else (if i.val < 2796 then (if i.val < 2794 then (if i.val < 2793 then 34 else 38) else (if i.val < 2795 then 73 else 49)) else (if i.val < 2798 then (if i.val < 2797 then 22 else 6) else (if i.val < 2799 then 86 else (if i.val < 2800 then 22 else 71)))))) else (if i.val < 2818 then (if i.val < 2809 then (if i.val < 2805 then (if i.val < 2803 then (if i.val < 2802 then 49 else 34) else (if i.val < 2804 then 57 else 75)) else (if i.val < 2807 then (if i.val < 2806 then 73 else 69) else (if i.val < 2808 then 22 else 24))) else (if i.val < 2813 then (if i.val < 2811 then (if i.val < 2810 then 49 else 60) else (if i.val < 2812 then 15 else 73)) else (if i.val < 2815 then (if i.val < 2814 then 73 else 49) else (if i.val < 2816 then 22 else (if i.val < 2817 then 49 else 49))))) else (if i.val < 2826 then (if i.val < 2822 then (if i.val < 2820 then (if i.val < 2819 then 46 else 10) else (if i.val < 2821 then 38 else 49)) else (if i.val < 2824 then (if i.val < 2823 then 13 else 32) else (if i.val < 2825 then 73 else 49))) else (if i.val < 2830 then (if i.val < 2828 then (if i.val < 2827 then 49 else 10) else (if i.val < 2829 then 57 else 30)) else (if i.val < 2832 then (if i.val < 2831 then 75 else 65) else (if i.val < 2833 then 22 else (if i.val < 2834 then 30 else 46)))))))) else (if i.val < 2902 then (if i.val < 2868 then (if i.val < 2851 then (if i.val < 2843 then (if i.val < 2839 then (if i.val < 2837 then (if i.val < 2836 then 4 else 38) else (if i.val < 2838 then 69 else 49)) else (if i.val < 2841 then (if i.val < 2840 then 46 else 16) else (if i.val < 2842 then 22 else 49))) else (if i.val < 2847 then (if i.val < 2845 then (if i.val < 2844 then 71 else 73) else (if i.val < 2846 then 10 else 66)) else (if i.val < 2849 then (if i.val < 2848 then 46 else 86) else (if i.val < 2850 then 16 else 49)))) else (if i.val < 2859 then (if i.val < 2855 then (if i.val < 2853 then (if i.val < 2852 then 49 else 60) else (if i.val < 2854 then 40 else 46)) else (if i.val < 2857 then (if i.val < 2856 then 60 else 57) else (if i.val < 2858 then 13 else 57))) else (if i.val < 2863 then (if i.val < 2861 then (if i.val < 2860 then 38 else 38) else (if i.val < 2862 then 49 else 73)) else (if i.val < 2865 then (if i.val < 2864 then 49 else 46) else (if i.val < 2866 then 16 else (if i.val < 2867 then 16 else 92)))))) else (if i.val < 2885 then (if i.val < 2876 then (if i.val < 2872 then (if i.val < 2870 then (if i.val < 2869 then 38 else 46) else (if i.val < 2871 then 86 else 4)) else (if i.val < 2874 then (if i.val < 2873 then 16 else 46) else (if i.val < 2875 then 34 else 57))) else (if i.val < 2880 then (if i.val < 2878 then (if i.val < 2877 then 71 else 46) else (if i.val < 2879 then 16 else 60)) else (if i.val < 2882 then (if i.val < 2881 then 60 else 75) else (if i.val < 2883 then 57 else (if i.val < 2884 then 49 else 15))))) else (if i.val < 2893 then (if i.val < 2889 then (if i.val < 2887 then (if i.val < 2886 then 60 else 38) else (if i.val < 2888 then 49 else 71)) else (if i.val < 2891 then (if i.val < 2890 then 34 else 69) else (if i.val < 2892 then 22 else 86))) else (if i.val < 2897 then (if i.val < 2895 then (if i.val < 2894 then 49 else 60) else (if i.val < 2896 then 49 else 86)) else (if i.val < 2899 then (if i.val < 2898 then 49 else 49) else (if i.val < 2900 then 60 else (if i.val < 2901 then 34 else 38))))))) else (if i.val < 2936 then (if i.val < 2919 then (if i.val < 2910 then (if i.val < 2906 then (if i.val < 2904 then (if i.val < 2903 then 73 else 49) else (if i.val < 2905 then 38 else 49)) else (if i.val < 2908 then (if i.val < 2907 then 46 else 16) else (if i.val < 2909 then 49 else 71))) else (if i.val < 2914 then (if i.val < 2912 then (if i.val < 2911 then 73 else 38) else (if i.val < 2913 then 86 else 16)) else (if i.val < 2916 then (if i.val < 2915 then 49 else 16) else (if i.val < 2917 then 60 else (if i.val < 2918 then 40 else 10))))) else (if i.val < 2927 then (if i.val < 2923 then (if i.val < 2921 then (if i.val < 2920 then 40 else 13) else (if i.val < 2922 then 38 else 49)) else (if i.val < 2925 then (if i.val < 2924 then 16 else 16) else (if i.val < 2926 then 92 else 46))) else (if i.val < 2931 then (if i.val < 2929 then (if i.val < 2928 then 4 else 16) else (if i.val < 2930 then 34 else 71)) else (if i.val < 2933 then (if i.val < 2932 then 46 else 16) else (if i.val < 2934 then 57 else (if i.val < 2935 then 60 else 10)))))) else (if i.val < 2953 then (if i.val < 2944 then (if i.val < 2940 then (if i.val < 2938 then (if i.val < 2937 then 60 else 30) else (if i.val < 2939 then 22 else 30)) else (if i.val < 2942 then (if i.val < 2941 then 73 else 69) else (if i.val < 2943 then 73 else 30))) else (if i.val < 2948 then (if i.val < 2946 then (if i.val < 2945 then 22 else 86) else (if i.val < 2947 then 57 else 22)) else (if i.val < 2950 then (if i.val < 2949 then 46 else 49) else (if i.val < 2951 then 21 else (if i.val < 2952 then 46 else 38))))) else (if i.val < 2961 then (if i.val < 2957 then (if i.val < 2955 then (if i.val < 2954 then 46 else 57) else (if i.val < 2956 then 34 else 49)) else (if i.val < 2959 then (if i.val < 2958 then 35 else 10) else (if i.val < 2960 then 57 else 21))) else (if i.val < 2965 then (if i.val < 2963 then (if i.val < 2962 then 49 else 73) else (if i.val < 2964 then 13 else 73)) else (if i.val < 2967 then (if i.val < 2966 then 86 else 16) else (if i.val < 2968 then 21 else (if i.val < 2969 then 22 else 86))))))))) else (if i.val < 3105 then (if i.val < 3037 then (if i.val < 3003 then (if i.val < 2986 then (if i.val < 2978 then (if i.val < 2974 then (if i.val < 2972 then (if i.val < 2971 then 73 else 16) else (if i.val < 2973 then 32 else 46)) else (if i.val < 2976 then (if i.val < 2975 then 38 else 35) else (if i.val < 2977 then 69 else 10))) else (if i.val < 2982 then (if i.val < 2980 then (if i.val < 2979 then 60 else 57) else (if i.val < 2981 then 21 else 57)) else (if i.val < 2984 then (if i.val < 2983 then 21 else 49) else (if i.val < 2985 then 57 else 73)))) else (if i.val < 2994 then (if i.val < 2990 then (if i.val < 2988 then (if i.val < 2987 then 57 else 22) else (if i.val < 2989 then 46 else 57)) else (if i.val < 2992 then (if i.val < 2991 then 21 else 46) else (if i.val < 2993 then 57 else 57))) else (if i.val < 2998 then (if i.val < 2996 then (if i.val < 2995 then 49 else 13) else (if i.val < 2997 then 73 else 16)) else (if i.val < 3000 then (if i.val < 2999 then 21 else 49) else (if i.val < 3001 then 60 else (if i.val < 3002 then 38 else 32)))))) else (if i.val < 3020 then (if i.val < 3011 then (if i.val < 3007 then (if i.val < 3005 then (if i.val < 3004 then 69 else 60) else (if i.val < 3006 then 21 else 57)) else (if i.val < 3009 then (if i.val < 3008 then 10 else 46) else (if i.val < 3010 then 21 else 57))) else (if i.val < 3015 then (if i.val < 3013 then (if i.val < 3012 then 57 else 21) else (if i.val < 3014 then 49 else 35)) else (if i.val < 3017 then (if i.val < 3016 then 21 else 60) else (if i.val < 3018 then 35 else (if i.val < 3019 then 69 else 60))))) else (if i.val < 3028 then (if i.val < 3024 then (if i.val < 3022 then (if i.val < 3021 then 21 else 57) else (if i.val < 3023 then 21 else 49)) else (if i.val < 3026 then (if i.val < 3025 then 21 else 21) else (if i.val < 3027 then 49 else 38))) else (if i.val < 3032 then (if i.val < 3030 then (if i.val < 3029 then 73 else 46) else (if i.val < 3031 then 92 else 21)) else (if i.val < 3034 then (if i.val < 3033 then 92 else 13) else (if i.val < 3035 then 46 else (if i.val < 3036 then 46 else 60))))))) else (if i.val < 3071 then (if i.val < 3054 then (if i.val < 3045 then (if i.val < 3041 then (if i.val < 3039 then (if i.val < 3038 then 86 else 16) else (if i.val < 3040 then 57 else 38)) else (if i.val < 3043 then (if i.val < 3042 then 47 else 46) else (if i.val < 3044 then 16 else 57))) else (if i.val < 3049 then (if i.val < 3047 then (if i.val < 3046 then 71 else 4) else (if i.val < 3048 then 71 else 15)) else (if i.val < 3051 then (if i.val < 3050 then 16 else 57) else (if i.val < 3052 then 21 else (if i.val < 3053 then 46 else 60))))) else (if i.val < 3062 then (if i.val < 3058 then (if i.val < 3056 then (if i.val < 3055 then 69 else 92) else (if i.val < 3057 then 34 else 60)) else (if i.val < 3060 then (if i.val < 3059 then 57 else 21) else (if i.val < 3061 then 38 else 16))) else (if i.val < 3066 then (if i.val < 3064 then (if i.val < 3063 then 21 else 69) else (if i.val < 3065 then 47 else 38)) else (if i.val < 3068 then (if i.val < 3067 then 49 else 38) else (if i.val < 3069 then 86 else (if i.val < 3070 then 16 else 57)))))) else (if i.val < 3088 then (if i.val < 3079 then (if i.val < 3075 then (if i.val < 3073 then (if i.val < 3072 then 46 else 60) else (if i.val < 3074 then 16 else 13)) else (if i.val < 3077 then (if i.val < 3076 then 21 else 49) else (if i.val < 3078 then 34 else 21))) else (if i.val < 3083 then (if i.val < 3081 then (if i.val < 3080 then 47 else 57) else (if i.val < 3082 then 40 else 21)) else (if i.val < 3085 then (if i.val < 3084 then 4 else 16) else (if i.val < 3086 then 21 else (if i.val < 3087 then 13 else 71))))) else (if i.val < 3096 then (if i.val < 3092 then (if i.val < 3090 then (if i.val < 3089 then 60 else 38) else (if i.val < 3091 then 21 else 35)) else (if i.val < 3094 then (if i.val < 3093 then 40 else 69) else (if i.val < 3095 then 38 else 92))) else (if i.val < 3100 then (if i.val < 3098 then (if i.val < 3097 then 60 else 21) else (if i.val < 3099 then 21 else 57)) else (if i.val < 3102 then (if i.val < 3101 then 40 else 26) else (if i.val < 3103 then 26 else (if i.val < 3104 then 57 else 21)))))))) else (if i.val < 3172 then (if i.val < 3138 then (if i.val < 3121 then (if i.val < 3113 then (if i.val < 3109 then (if i.val < 3107 then (if i.val < 3106 then 21 else 47) else (if i.val < 3108 then 16 else 13)) else (if i.val < 3111 then (if i.val < 3110 then 49 else 92) else (if i.val < 3112 then 16 else 4))) else (if i.val < 3117 then (if i.val < 3115 then (if i.val < 3114 then 21 else 46) else (if i.val < 3116 then 60 else 92)) else (if i.val < 3119 then (if i.val < 3118 then 40 else 26) else (if i.val < 3120 then 92 else 60)))) else (if i.val < 3129 then (if i.val < 3125 then (if i.val < 3123 then (if i.val < 3122 then 21 else 34) else (if i.val < 3124 then 4 else 46)) else (if i.val < 3127 then (if i.val < 3126 then 60 else 38) else (if i.val < 3128 then 16 else 16))) else (if i.val < 3133 then (if i.val < 3131 then (if i.val < 3130 then 21 else 47) else (if i.val < 3132 then 40 else 71)) else (if i.val < 3135 then (if i.val < 3134 then 40 else 71) else (if i.val < 3136 then 49 else (if i.val < 3137 then 40 else 34)))))) else (if i.val < 3155 then (if i.val < 3146 then (if i.val < 3142 then (if i.val < 3140 then (if i.val < 3139 then 40 else 11) else (if i.val < 3141 then 38 else 49)) else (if i.val < 3144 then (if i.val < 3143 then 26 else 66) else (if i.val < 3145 then 4 else 71))) else (if i.val < 3150 then (if i.val < 3148 then (if i.val < 3147 then 40 else 71) else (if i.val < 3149 then 49 else 71)) else (if i.val < 3152 then (if i.val < 3151 then 56 else 15) else (if i.val < 3153 then 38 else (if i.val < 3154 then 46 else 46))))) else (if i.val < 3163 then (if i.val < 3159 then (if i.val < 3157 then (if i.val < 3156 then 16 else 69) else (if i.val < 3158 then 16 else 71)) else (if i.val < 3161 then (if i.val < 3160 then 38 else 47) else (if i.val < 3162 then 32 else 38))) else (if i.val < 3167 then (if i.val < 3165 then (if i.val < 3164 then 21 else 40) else (if i.val < 3166 then 49 else 16)) else (if i.val < 3169 then (if i.val < 3168 then 71 else 69) else (if i.val < 3170 then 49 else (if i.val < 3171 then 30 else 92))))))) else (if i.val < 3206 then (if i.val < 3189 then (if i.val < 3180 then (if i.val < 3176 then (if i.val < 3174 then (if i.val < 3173 then 40 else 34) else (if i.val < 3175 then 21 else 21)) else (if i.val < 3178 then (if i.val < 3177 then 40 else 26) else (if i.val < 3179 then 60 else 18))) else (if i.val < 3184 then (if i.val < 3182 then (if i.val < 3181 then 34 else 71) else (if i.val < 3183 then 38 else 49)) else (if i.val < 3186 then (if i.val < 3185 then 38 else 26) else (if i.val < 3187 then 47 else (if i.val < 3188 then 16 else 38))))) else (if i.val < 3197 then (if i.val < 3193 then (if i.val < 3191 then (if i.val < 3190 then 21 else 84) else (if i.val < 3192 then 47 else 57)) else (if i.val < 3195 then (if i.val < 3194 then 38 else 47) else (if i.val < 3196 then 49 else 38))) else (if i.val < 3201 then (if i.val < 3199 then (if i.val < 3198 then 46 else 57) else (if i.val < 3200 then 86 else 16)) else (if i.val < 3203 then (if i.val < 3202 then 71 else 16) else (if i.val < 3204 then 60 else (if i.val < 3205 then 38 else 16)))))) else (if i.val < 3223 then (if i.val < 3214 then (if i.val < 3210 then (if i.val < 3208 then (if i.val < 3207 then 71 else 30) else (if i.val < 3209 then 60 else 21)) else (if i.val < 3212 then (if i.val < 3211 then 13 else 57) else (if i.val < 3213 then 38 else 38))) else (if i.val < 3218 then (if i.val < 3216 then (if i.val < 3215 then 40 else 71) else (if i.val < 3217 then 49 else 47)) else (if i.val < 3220 then (if i.val < 3219 then 40 else 49) else (if i.val < 3221 then 21 else (if i.val < 3222 then 47 else 60))))) else (if i.val < 3231 then (if i.val < 3227 then (if i.val < 3225 then (if i.val < 3224 then 21 else 66) else (if i.val < 3226 then 4 else 71)) else (if i.val < 3229 then (if i.val < 3228 then 16 else 21) else (if i.val < 3230 then 21 else 47))) else (if i.val < 3235 then (if i.val < 3233 then (if i.val < 3232 then 13 else 15) else (if i.val < 3234 then 40 else 71)) else (if i.val < 3237 then (if i.val < 3236 then 49 else 11) else (if i.val < 3238 then 40 else (if i.val < 3239 then 26 else 57))))))))))) else (if i.val < 3780 then (if i.val < 3510 then (if i.val < 3375 then (if i.val < 3307 then (if i.val < 3273 then (if i.val < 3256 then (if i.val < 3248 then (if i.val < 3244 then (if i.val < 3242 then (if i.val < 3241 then 40 else 66) else (if i.val < 3243 then 69 else 49)) else (if i.val < 3246 then (if i.val < 3245 then 38 else 26) else (if i.val < 3247 then 34 else 71))) else (if i.val < 3252 then (if i.val < 3250 then (if i.val < 3249 then 47 else 15) else (if i.val < 3251 then 40 else 71)) else (if i.val < 3254 then (if i.val < 3253 then 40 else 26) else (if i.val < 3255 then 26 else 66)))) else (if i.val < 3264 then (if i.val < 3260 then (if i.val < 3258 then (if i.val < 3257 then 69 else 21) else (if i.val < 3259 then 26 else 47)) else (if i.val < 3262 then (if i.val < 3261 then 57 else 13) else (if i.val < 3263 then 49 else 40))) else (if i.val < 3268 then (if i.val < 3266 then (if i.val < 3265 then 49 else 26) else (if i.val < 3267 then 49 else 49)) else (if i.val < 3270 then (if i.val < 3269 then 46 else 21) else (if i.val < 3271 then 46 else (if i.val < 3272 then 57 else 16)))))) else (if i.val < 3290 then (if i.val < 3281 then (if i.val < 3277 then (if i.val < 3275 then (if i.val < 3274 then 38 else 71) else (if i.val < 3276 then 47 else 46)) else (if i.val < 3279 then (if i.val < 3278 then 16 else 46) else (if i.val < 3280 then 69 else 21))) else (if i.val < 3285 then (if i.val < 3283 then (if i.val < 3282 then 26 else 57) else (if i.val < 3284 then 69 else 34)) else (if i.val < 3287 then (if i.val < 3286 then 21 else 57) else (if i.val < 3288 then 4 else (if i.val < 3289 then 21 else 71))))) else (if i.val < 3298 then (if i.val < 3294 then (if i.val < 3292 then (if i.val < 3291 then 47 else 16) else (if i.val < 3293 then 45 else 71)) else (if i.val < 3296 then (if i.val < 3295 then 21 else 60) else (if i.val < 3297 then 60 else 46))) else (if i.val < 3302 then (if i.val < 3300 then (if i.val < 3299 then 57 else 34) else (if i.val < 3301 then 21 else 4)) else (if i.val < 3304 then (if i.val < 3303 then 21 else 71) else (if i.val < 3305 then 84 else (if i.val < 3306 then 47 else 34))))))) else (if i.val < 3341 then (if i.val < 3324 then (if i.val < 3315 then (if i.val < 3311 then (if i.val < 3309 then (if i.val < 3308 then 46 else 32) else (if i.val < 3310 then 16 else 49)) else (if i.val < 3313 then (if i.val < 3312 then 13 else 40) else (if i.val < 3314 then 26 else 47))) else (if i.val < 3319 then (if i.val < 3317 then (if i.val < 3316 then 40 else 34) else (if i.val < 3318 then 47 else 40)) else (if i.val < 3321 then (if i.val < 3320 then 11 else 66) else (if i.val < 3322 then 40 else (if i.val < 3323 then 49 else 49))))) else (if i.val < 3332 then (if i.val < 3328 then (if i.val < 3326 then (if i.val < 3325 then 6 else 21) else (if i.val < 3327 then 71 else 47)) else (if i.val < 3330 then (if i.val < 3329 then 40 else 49) else (if i.val < 3331 then 56 else 15))) else (if i.val < 3336 then (if i.val < 3334 then (if i.val < 3333 then 69 else 26) else (if i.val < 3335 then 71 else 49)) else (if i.val < 3338 then (if i.val < 3337 then 30 else 57) else (if i.val < 3339 then 69 else (if i.val < 3340 then 47 else 57)))))) else (if i.val < 3358 then (if i.val < 3349 then (if i.val < 3345 then (if i.val < 3343 then (if i.val < 3342 then 71 else 38) else (if i.val < 3344 then 46 else 57)) else (if i.val < 3347 then (if i.val < 3346 then 21 else 38) else (if i.val < 3348 then 49 else 57))) else (if i.val < 3353 then (if i.val < 3351 then (if i.val < 3350 then 32 else 71) else (if i.val < 3352 then 38 else 21)) else (if i.val < 3355 then (if i.val < 3354 then 26 else 49) else (if i.val < 3356 then 49 else (if i.val < 3357 then 30 else 21))))) else (if i.val < 3366 then (if i.val < 3362 then (if i.val < 3360 then (if i.val < 3359 then 71 else 56) else (if i.val < 3361 then 69 else 49)) else (if i.val < 3364 then (if i.val < 3363 then 92 else 21) else (if i.val < 3365 then 21 else 26))) else (if i.val < 3370 then (if i.val < 3368 then (if i.val < 3367 then 13 else 49) else (if i.val < 3369 then 26 else 30)) else (if i.val < 3372 then (if i.val < 3371 then 22 else 46) else (if i.val < 3373 then 92 else (if i.val < 3374 then 40 else 60)))))))) else (if i.val < 3442 then (if i.val < 3408 then (if i.val < 3391 then (if i.val < 3383 then (if i.val < 3379 then (if i.val < 3377 then (if i.val < 3376 then 26 else 60) else (if i.val < 3378 then 18 else 11)) else (if i.val < 3381 then (if i.val < 3380 then 49 else 30) else (if i.val < 3382 then 38 else 47))) else (if i.val < 3387 then (if i.val < 3385 then (if i.val < 3384 then 49 else 34) else (if i.val < 3386 then 38 else 26)) else (if i.val < 3389 then (if i.val < 3388 then 38 else 15) else (if i.val < 3390 then 16 else 38)))) else (if i.val < 3399 then (if i.val < 3395 then (if i.val < 3393 then (if i.val < 3392 then 26 else 57) else (if i.val < 3394 then 21 else 26)) else (if i.val < 3397 then (if i.val < 3396 then 47 else 30) else (if i.val < 3398 then 40 else 13))) else (if i.val < 3403 then (if i.val < 3401 then (if i.val < 3400 then 60 else 92) else (if i.val < 3402 then 26 else 40)) else (if i.val < 3405 then (if i.val < 3404 then 84 else 56) else (if i.val < 3406 then 40 else (if i.val < 3407 then 22 else 38)))))) else (if i.val < 3425 then (if i.val < 3416 then (if i.val < 3412 then (if i.val < 3410 then (if i.val < 3409 then 21 else 71) else (if i.val < 3411 then 47 else 30)) else (if i.val < 3414 then (if i.val < 3413 then 57 else 26) else (if i.val < 3415 then 38 else 47))) else (if i.val < 3420 then (if i.val < 3418 then (if i.val < 3417 then 49 else 47) else (if i.val < 3419 then 11 else 49)) else (if i.val < 3422 then (if i.val < 3421 then 45 else 47) else (if i.val < 3423 then 38 else (if i.val < 3424 then 21 else 60))))) else (if i.val < 3433 then (if i.val < 3429 then (if i.val < 3427 then (if i.val < 3426 then 84 else 66) else (if i.val < 3428 then 47 else 21)) else (if i.val < 3431 then (if i.val < 3430 then 49 else 6) else (if i.val < 3432 then 21 else 16))) else (if i.val < 3437 then (if i.val < 3435 then (if i.val < 3434 then 26 else 13) else (if i.val < 3436 then 66 else 38)) else (if i.val < 3439 then (if i.val < 3438 then 47 else 66) else (if i.val < 3440 then 30 else (if i.val < 3441 then 49 else 40))))))) else (if i.val < 3476 then (if i.val < 3459 then (if i.val < 3450 then (if i.val < 3446 then (if i.val < 3444 then (if i.val < 3443 then 26 else 57) else (if i.val < 3445 then 30 else 75)) else (if i.val < 3448 then (if i.val < 3447 then 84 else 26) else (if i.val < 3449 then 11 else 57))) else (if i.val < 3454 then (if i.val < 3452 then (if i.val < 3451 then 66 else 6) else (if i.val < 3453 then 84 else 30)) else (if i.val < 3456 then (if i.val < 3455 then 34 else 56) else (if i.val < 3457 then 57 else (if i.val < 3458 then 73 else 92))))) else (if i.val < 3467 then (if i.val < 3463 then (if i.val < 3461 then (if i.val < 3460 then 69 else 47) else (if i.val < 3462 then 45 else 26)) else (if i.val < 3465 then (if i.val < 3464 then 66 else 69) else (if i.val < 3466 then 69 else 47))) else (if i.val < 3471 then (if i.val < 3469 then (if i.val < 3468 then 21 else 13) else (if i.val < 3470 then 26 else 47)) else (if i.val < 3473 then (if i.val < 3472 then 38 else 30) else (if i.val < 3474 then 49 else (if i.val < 3475 then 38 else 30)))))) else (if i.val < 3493 then (if i.val < 3484 then (if i.val < 3480 then (if i.val < 3478 then (if i.val < 3477 then 30 else 49) else (if i.val < 3479 then 30 else 34)) else (if i.val < 3482 then (if i.val < 3481 then 21 else 13) else (if i.val < 3483 then 46 else 32))) else (if i.val < 3488 then (if i.val < 3486 then (if i.val < 3485 then 21 else 16) else (if i.val < 3487 then 47 else 16)) else (if i.val < 3490 then (if i.val < 3489 then 4 else 71) else (if i.val < 3491 then 15 else (if i.val < 3492 then 16 else 60))))) else (if i.val < 3501 then (if i.val < 3497 then (if i.val < 3495 then (if i.val < 3494 then 26 else 47) else (if i.val < 3496 then 38 else 46)) else (if i.val < 3499 then (if i.val < 3498 then 57 else 60) else (if i.val < 3500 then 13 else 35))) else (if i.val < 3505 then (if i.val < 3503 then (if i.val < 3502 then 49 else 38) else (if i.val < 3504 then 84 else 21)) else (if i.val < 3507 then (if i.val < 3506 then 49 else 4) else (if i.val < 3508 then 13 else (if i.val < 3509 then 71 else 56))))))))) else (if i.val < 3645 then (if i.val < 3577 then (if i.val < 3543 then (if i.val < 3526 then (if i.val < 3518 then (if i.val < 3514 then (if i.val < 3512 then (if i.val < 3511 then 47 else 45) else (if i.val < 3513 then 21 else 26)) else (if i.val < 3516 then (if i.val < 3515 then 13 else 46) else (if i.val < 3517 then 92 else 49))) else (if i.val < 3522 then (if i.val < 3520 then (if i.val < 3519 then 16 else 21) else (if i.val < 3521 then 46 else 40)) else (if i.val < 3524 then (if i.val < 3523 then 21 else 35) else (if i.val < 3525 then 21 else 18)))) else (if i.val < 3534 then (if i.val < 3530 then (if i.val < 3528 then (if i.val < 3527 then 49 else 47) else (if i.val < 3529 then 47 else 57)) else (if i.val < 3532 then (if i.val < 3531 then 32 else 16) else (if i.val < 3533 then 30 else 60))) else (if i.val < 3538 then (if i.val < 3536 then (if i.val < 3535 then 40 else 13) else (if i.val < 3537 then 40 else 47)) else (if i.val < 3540 then (if i.val < 3539 then 26 else 26) else (if i.val < 3541 then 66 else (if i.val < 3542 then 71 else 47)))))) else (if i.val < 3560 then (if i.val < 3551 then (if i.val < 3547 then (if i.val < 3545 then (if i.val < 3544 then 11 else 30) else (if i.val < 3546 then 26 else 57)) else (if i.val < 3549 then (if i.val < 3548 then 26 else 66) else (if i.val < 3550 then 49 else 47))) else (if i.val < 3555 then (if i.val < 3553 then (if i.val < 3552 then 15 else 40) else (if i.val < 3554 then 66 else 69)) else (if i.val < 3557 then (if i.val < 3556 then 26 else 57) else (if i.val < 3558 then 66 else (if i.val < 3559 then 57 else 21))))) else (if i.val < 3568 then (if i.val < 3564 then (if i.val < 3562 then (if i.val < 3561 then 57 else 16) else (if i.val < 3563 then 69 else 26)) else (if i.val < 3566 then (if i.val < 3565 then 49 else 34) else (if i.val < 3567 then 45 else 21))) else (if i.val < 3572 then (if i.val < 3570 then (if i.val < 3569 then 84 else 60) else (if i.val < 3571 then 57 else 38)) else (if i.val < 3574 then (if i.val < 3573 then 84 else 18) else (if i.val < 3575 then 84 else (if i.val < 3576 then 34 else 38))))))) else (if i.val < 3611 then (if i.val < 3594 then (if i.val < 3585 then (if i.val < 3581 then (if i.val < 3579 then (if i.val < 3578 then 71 else 47) else (if i.val < 3580 then 30 else 47)) else (if i.val < 3583 then (if i.val < 3582 then 26 else 66) else (if i.val < 3584 then 49 else 49))) else (if i.val < 3589 then (if i.val < 3587 then (if i.val < 3586 then 6 else 47) else (if i.val < 3588 then 56 else 15)) else (if i.val < 3591 then (if i.val < 3590 then 26 else 49) else (if i.val < 3592 then 71 else (if i.val < 3593 then 15 else 57))))) else (if i.val < 3602 then (if i.val < 3598 then (if i.val < 3596 then (if i.val < 3595 then 49 else 57) else (if i.val < 3597 then 49 else 57)) else (if i.val < 3600 then (if i.val < 3599 then 92 else 40) else (if i.val < 3601 then 26 else 45))) else (if i.val < 3606 then (if i.val < 3604 then (if i.val < 3603 then 57 else 26) else (if i.val < 3605 then 22 else 26)) else (if i.val < 3608 then (if i.val < 3607 then 30 else 57) else (if i.val < 3609 then 40 else (if i.val < 3610 then 40 else 13)))))) else (if i.val < 3628 then (if i.val < 3619 then (if i.val < 3615 then (if i.val < 3613 then (if i.val < 3612 then 60 else 66) else (if i.val < 3614 then 40 else 18)) else (if i.val < 3617 then (if i.val < 3616 then 22 else 75) else (if i.val < 3618 then 49 else 45))) else (if i.val < 3623 then (if i.val < 3621 then (if i.val < 3620 then 45 else 26) else (if i.val < 3622 then 34 else 38)) else (if i.val < 3625 then (if i.val < 3624 then 11 else 66) else (if i.val < 3626 then 73 else (if i.val < 3627 then 49 else 84))))) else (if i.val < 3636 then (if i.val < 3632 then (if i.val < 3630 then (if i.val < 3629 then 6 else 26) else (if i.val < 3631 then 30 else 45)) else (if i.val < 3634 then (if i.val < 3633 then 66 else 49) else (if i.val < 3635 then 13 else 47))) else (if i.val < 3640 then (if i.val < 3638 then (if i.val < 3637 then 30 else 13) else (if i.val < 3639 then 71 else 60)) else (if i.val < 3642 then (if i.val < 3641 then 21 else 92) else (if i.val < 3643 then 26 else (if i.val < 3644 then 21 else 16)))))))) else (if i.val < 3712 then (if i.val < 3678 then (if i.val < 3661 then (if i.val < 3653 then (if i.val < 3649 then (if i.val < 3647 then (if i.val < 3646 then 49 else 84) else (if i.val < 3648 then 49 else 13)) else (if i.val < 3651 then (if i.val < 3650 then 56 else 26) else (if i.val < 3652 then 16 else 21))) else (if i.val < 3657 then (if i.val < 3655 then (if i.val < 3654 then 60 else 40) else (if i.val < 3656 then 11 else 49)) else (if i.val < 3659 then (if i.val < 3658 then 71 else 47) else (if i.val < 3660 then 30 else 38)))) else (if i.val < 3669 then (if i.val < 3665 then (if i.val < 3663 then (if i.val < 3662 then 57 else 71) else (if i.val < 3664 then 38 else 30)) else (if i.val < 3667 then (if i.val < 3666 then 15 else 49) else (if i.val < 3668 then 66 else 15))) else (if i.val < 3673 then (if i.val < 3671 then (if i.val < 3670 then 26 else 66) else (if i.val < 3672 then 30 else 69)) else (if i.val < 3675 then (if i.val < 3674 then 38 else 69) else (if i.val < 3676 then 47 else (if i.val < 3677 then 60 else 34)))))) else (if i.val < 3695 then (if i.val < 3686 then (if i.val < 3682 then (if i.val < 3680 then (if i.val < 3679 then 38 else 38) else (if i.val < 3681 then 49 else 30)) else (if i.val < 3684 then (if i.val < 3683 then 47 else 30) else (if i.val < 3685 then 6 else 47))) else (if i.val < 3690 then (if i.val < 3688 then (if i.val < 3687 then 49 else 15) else (if i.val < 3689 then 15 else 21)) else (if i.val < 3692 then (if i.val < 3691 then 26 else 66) else (if i.val < 3693 then 22 else (if i.val < 3694 then 46 else 47))))) else (if i.val < 3703 then (if i.val < 3699 then (if i.val < 3697 then (if i.val < 3696 then 22 else 30) else (if i.val < 3698 then 40 else 13)) else (if i.val < 3701 then (if i.val < 3700 then 40 else 38) else (if i.val < 3702 then 30 else 22))) else (if i.val < 3707 then (if i.val < 3705 then (if i.val < 3704 then 75 else 57) else (if i.val < 3706 then 69 else 30)) else (if i.val < 3709 then (if i.val < 3708 then 57 else 6) else (if i.val < 3710 then 34 else (if i.val < 3711 then 11 else 66))))))) else (if i.val < 3746 then (if i.val < 3729 then (if i.val < 3720 then (if i.val < 3716 then (if i.val < 3714 then (if i.val < 3713 then 49 else 84) else (if i.val < 3715 then 57 else 30)) else (if i.val < 3718 then (if i.val < 3717 then 30 else 15) else (if i.val < 3719 then 38 else 30))) else (if i.val < 3724 then (if i.val < 3722 then (if i.val < 3721 then 46 else 92) else (if i.val < 3723 then 21 else 47)) else (if i.val < 3726 then (if i.val < 3725 then 49 else 57) else (if i.val < 3727 then 30 else (if i.val < 3728 then 15 else 26))))) else (if i.val < 3737 then (if i.val < 3733 then (if i.val < 3731 then (if i.val < 3730 then 30 else 49) else (if i.val < 3732 then 13 else 30)) else (if i.val < 3735 then (if i.val < 3734 then 47 else 15) else (if i.val < 3736 then 46 else 47))) else (if i.val < 3741 then (if i.val < 3739 then (if i.val < 3738 then 73 else 30) else (if i.val < 3740 then 22 else 38)) else (if i.val < 3743 then (if i.val < 3742 then 57 else 40) else (if i.val < 3744 then 30 else (if i.val < 3745 then 75 else 69)))))) else (if i.val < 3763 then (if i.val < 3754 then (if i.val < 3750 then (if i.val < 3748 then (if i.val < 3747 then 66 else 6) else (if i.val < 3749 then 38 else 57)) else (if i.val < 3752 then (if i.val < 3751 then 69 else 73) else (if i.val < 3753 then 75 else 73))) else (if i.val < 3758 then (if i.val < 3756 then (if i.val < 3755 then 38 else 34) else (if i.val < 3757 then 49 else 47)) else (if i.val < 3760 then (if i.val < 3759 then 11 else 18) else (if i.val < 3761 then 69 else (if i.val < 3762 then 18 else 65))))) else (if i.val < 3771 then (if i.val < 3767 then (if i.val < 3765 then (if i.val < 3764 then 13 else 78) else (if i.val < 3766 then 69 else 38)) else (if i.val < 3769 then (if i.val < 3768 then 49 else 34) else (if i.val < 3770 then 18 else 66))) else (if i.val < 3775 then (if i.val < 3773 then (if i.val < 3772 then 46 else 65) else (if i.val < 3774 then 22 else 57)) else (if i.val < 3777 then (if i.val < 3776 then 78 else 65) else (if i.val < 3778 then 30 else (if i.val < 3779 then 49 else 22)))))))))) else (if i.val < 4050 then (if i.val < 3915 then (if i.val < 3847 then (if i.val < 3813 then (if i.val < 3796 then (if i.val < 3788 then (if i.val < 3784 then (if i.val < 3782 then (if i.val < 3781 then 38 else 18) else (if i.val < 3783 then 47 else 47)) else (if i.val < 3786 then (if i.val < 3785 then 30 else 46) else (if i.val < 3787 then 13 else 57))) else (if i.val < 3792 then (if i.val < 3790 then (if i.val < 3789 then 69 else 69) else (if i.val < 3791 then 34 else 73)) else (if i.val < 3794 then (if i.val < 3793 then 73 else 49) else (if i.val < 3795 then 38 else 22)))) else (if i.val < 3804 then (if i.val < 3800 then (if i.val < 3798 then (if i.val < 3797 then 46 else 69) else (if i.val < 3799 then 69 else 78)) else (if i.val < 3802 then (if i.val < 3801 then 65 else 69) else (if i.val < 3803 then 49 else 22))) else (if i.val < 3808 then (if i.val < 3806 then (if i.val < 3805 then 46 else 49) else (if i.val < 3807 then 15 else 30)) else (if i.val < 3810 then (if i.val < 3809 then 82 else 30) else (if i.val < 3811 then 11 else (if i.val < 3812 then 30 else 73)))))) else (if i.val < 3830 then (if i.val < 3821 then (if i.val < 3817 then (if i.val < 3815 then (if i.val < 3814 then 49 else 38) else (if i.val < 3816 then 6 else 69)) else (if i.val < 3819 then (if i.val < 3818 then 30 else 46) else (if i.val < 3820 then 38 else 15))) else (if i.val < 3825 then (if i.val < 3823 then (if i.val < 3822 then 78 else 22) else (if i.val < 3824 then 82 else 75)) else (if i.val < 3827 then (if i.val < 3826 then 73 else 10) else (if i.val < 3828 then 66 else (if i.val < 3829 then 22 else 57))))) else (if i.val < 3838 then (if i.val < 3834 then (if i.val < 3832 then (if i.val < 3831 then 73 else 6) else (if i.val < 3833 then 73 else 82)) else (if i.val < 3836 then (if i.val < 3835 then 30 else 22) else (if i.val < 3837 then 49 else 49))) else (if i.val < 3842 then (if i.val < 3840 then (if i.val < 3839 then 22 else 66) else (if i.val < 3841 then 30 else 22)) else (if i.val < 3844 then (if i.val < 3843 then 22 else 46) else (if i.val < 3845 then 69 else (if i.val < 3846 then 82 else 22))))))) else (if i.val < 3881 then (if i.val < 3864 then (if i.val < 3855 then (if i.val < 3851 then (if i.val < 3849 then (if i.val < 3848 then 30 else 22) else (if i.val < 3850 then 38 else 82)) else (if i.val < 3853 then (if i.val < 3852 then 22 else 86) else (if i.val < 3854 then 78 else 10))) else (if i.val < 3859 then (if i.val < 3857 then (if i.val < 3856 then 78 else 46) else (if i.val < 3858 then 49 else 22)) else (if i.val < 3861 then (if i.val < 3860 then 46 else 49) else (if i.val < 3862 then 22 else (if i.val < 3863 then 22 else 86))))) else (if i.val < 3872 then (if i.val < 3868 then (if i.val < 3866 then (if i.val < 3865 then 86 else 38) else (if i.val < 3867 then 34 else 73)) else (if i.val < 3870 then (if i.val < 3869 then 49 else 30) else (if i.val < 3871 then 69 else 22))) else (if i.val < 3876 then (if i.val < 3874 then (if i.val < 3873 then 82 else 22) else (if i.val < 3875 then 30 else 57)) else (if i.val < 3878 then (if i.val < 3877 then 57 else 82) else (if i.val < 3879 then 16 else (if i.val < 3880 then 46 else 49)))))) else (if i.val < 3898 then (if i.val < 3889 then (if i.val < 3885 then (if i.val < 3883 then (if i.val < 3882 then 6 else 46) else (if i.val < 3884 then 82 else 57)) else (if i.val < 3887 then (if i.val < 3886 then 22 else 49) else (if i.val < 3888 then 16 else 10))) else (if i.val < 3893 then (if i.val < 3891 then (if i.val < 3890 then 46 else 18) else (if i.val < 3892 then 73 else 22)) else (if i.val < 3895 then (if i.val < 3894 then 82 else 46) else (if i.val < 3896 then 34 else (if i.val < 3897 then 22 else 46))))) else (if i.val < 3906 then (if i.val < 3902 then (if i.val < 3900 then (if i.val < 3899 then 16 else 66) else (if i.val < 3901 then 82 else 78)) else (if i.val < 3904 then (if i.val < 3903 then 22 else 15) else (if i.val < 3905 then 78 else 10))) else (if i.val < 3910 then (if i.val < 3908 then (if i.val < 3907 then 46 else 60) else (if i.val < 3909 then 22 else 73)) else (if i.val < 3912 then (if i.val < 3911 then 86 else 66) else (if i.val < 3913 then 46 else (if i.val < 3914 then 73 else 82)))))))) else (if i.val < 3982 then (if i.val < 3948 then (if i.val < 3931 then (if i.val < 3923 then (if i.val < 3919 then (if i.val < 3917 then (if i.val < 3916 then 60 else 22) else (if i.val < 3918 then 22 else 82)) else (if i.val < 3921 then (if i.val < 3920 then 86 else 73) else (if i.val < 3922 then 78 else 82))) else (if i.val < 3927 then (if i.val < 3925 then (if i.val < 3924 then 21 else 6) else (if i.val < 3926 then 49 else 57)) else (if i.val < 3929 then (if i.val < 3928 then 30 else 49) else (if i.val < 3930 then 75 else 49)))) else (if i.val < 3939 then (if i.val < 3935 then (if i.val < 3933 then (if i.val < 3932 then 46 else 46) else (if i.val < 3934 then 46 else 82)) else (if i.val < 3937 then (if i.val < 3936 then 82 else 49) else (if i.val < 3938 then 13 else 30))) else (if i.val < 3943 then (if i.val < 3941 then (if i.val < 3940 then 49 else 57) else (if i.val < 3942 then 38 else 10)) else (if i.val < 3945 then (if i.val < 3944 then 57 else 78) else (if i.val < 3946 then 10 else (if i.val < 3947 then 92 else 18)))))) else (if i.val < 3965 then (if i.val < 3956 then (if i.val < 3952 then (if i.val < 3950 then (if i.val < 3949 then 46 else 46) else (if i.val < 3951 then 57 else 57)) else (if i.val < 3954 then (if i.val < 3953 then 82 else 49) else (if i.val < 3955 then 22 else 22))) else (if i.val < 3960 then (if i.val < 3958 then (if i.val < 3957 then 49 else 86) else (if i.val < 3959 then 86 else 57)) else (if i.val < 3962 then (if i.val < 3961 then 60 else 60) else (if i.val < 3963 then 16 else (if i.val < 3964 then 82 else 49))))) else (if i.val < 3973 then (if i.val < 3969 then (if i.val < 3967 then (if i.val < 3966 then 30 else 82) else (if i.val < 3968 then 86 else 71)) else (if i.val < 3971 then (if i.val < 3970 then 75 else 66) else (if i.val < 3972 then 82 else 6))) else (if i.val < 3977 then (if i.val < 3975 then (if i.val < 3974 then 46 else 46) else (if i.val < 3976 then 22 else 10)) else (if i.val < 3979 then (if i.val < 3978 then 73 else 26) else (if i.val < 3980 then 22 else (if i.val < 3981 then 38 else 38))))))) else (if i.val < 4016 then (if i.val < 3999 then (if i.val < 3990 then (if i.val < 3986 then (if i.val < 3984 then (if i.val < 3983 then 15 else 30) else (if i.val < 3985 then 60 else 6)) else (if i.val < 3988 then (if i.val < 3987 then 82 else 13) else (if i.val < 3989 then 49 else 49))) else (if i.val < 3994 then (if i.val < 3992 then (if i.val < 3991 then 60 else 46) else (if i.val < 3993 then 82 else 34)) else (if i.val < 3996 then (if i.val < 3995 then 49 else 66) else (if i.val < 3997 then 46 else (if i.val < 3998 then 34 else 46))))) else (if i.val < 4007 then (if i.val < 4003 then (if i.val < 4001 then (if i.val < 4000 then 49 else 15) else (if i.val < 4002 then 66 else 49)) else (if i.val < 4005 then (if i.val < 4004 then 60 else 78) else (if i.val < 4006 then 10 else 60))) else (if i.val < 4011 then (if i.val < 4009 then (if i.val < 4008 then 38 else 46) else (if i.val < 4010 then 10 else 38)) else (if i.val < 4013 then (if i.val < 4012 then 82 else 49) else (if i.val < 4014 then 21 else (if i.val < 4015 then 6 else 38)))))) else (if i.val < 4033 then (if i.val < 4024 then (if i.val < 4020 then (if i.val < 4018 then (if i.val < 4017 then 46 else 15) else (if i.val < 4019 then 6 else 49)) else (if i.val < 4022 then (if i.val < 4021 then 82 else 49) else (if i.val < 4023 then 82 else 34))) else (if i.val < 4028 then (if i.val < 4026 then (if i.val < 4025 then 13 else 49) else (if i.val < 4027 then 92 else 49)) else (if i.val < 4030 then (if i.val < 4029 then 86 else 49) else (if i.val < 4031 then 30 else (if i.val < 4032 then 57 else 46))))) else (if i.val < 4041 then (if i.val < 4037 then (if i.val < 4035 then (if i.val < 4034 then 82 else 86) else (if i.val < 4036 then 86 else 46)) else (if i.val < 4039 then (if i.val < 4038 then 38 else 57) else (if i.val < 4040 then 71 else 38))) else (if i.val < 4045 then (if i.val < 4043 then (if i.val < 4042 then 75 else 57) else (if i.val < 4044 then 60 else 34)) else (if i.val < 4047 then (if i.val < 4046 then 82 else 34) else (if i.val < 4048 then 21 else (if i.val < 4049 then 13 else 10))))))))) else (if i.val < 4185 then (if i.val < 4117 then (if i.val < 4083 then (if i.val < 4066 then (if i.val < 4058 then (if i.val < 4054 then (if i.val < 4052 then (if i.val < 4051 then 46 else 60) else (if i.val < 4053 then 73 else 60)) else (if i.val < 4056 then (if i.val < 4055 then 49 else 10) else (if i.val < 4057 then 38 else 16))) else (if i.val < 4062 then (if i.val < 4060 then (if i.val < 4059 then 78 else 18) else (if i.val < 4061 then 57 else 46)) else (if i.val < 4064 then (if i.val < 4063 then 46 else 57) else (if i.val < 4065 then 49 else 73)))) else (if i.val < 4074 then (if i.val < 4070 then (if i.val < 4068 then (if i.val < 4067 then 10 else 46) else (if i.val < 4069 then 57 else 46)) else (if i.val < 4072 then (if i.val < 4071 then 34 else 47) else (if i.val < 4073 then 71 else 71))) else (if i.val < 4078 then (if i.val < 4076 then (if i.val < 4075 then 40 else 82) else (if i.val < 4077 then 35 else 57)) else (if i.val < 4080 then (if i.val < 4079 then 34 else 38) else (if i.val < 4081 then 57 else (if i.val < 4082 then 46 else 38)))))) else (if i.val < 4100 then (if i.val < 4091 then (if i.val < 4087 then (if i.val < 4085 then (if i.val < 4084 then 78 else 15) else (if i.val < 4086 then 32 else 49)) else (if i.val < 4089 then (if i.val < 4088 then 66 else 24) else (if i.val < 4090 then 46 else 82))) else (if i.val < 4095 then (if i.val < 4093 then (if i.val < 4092 then 32 else 46) else (if i.val < 4094 then 22 else 82)) else (if i.val < 4097 then (if i.val < 4096 then 13 else 22) else (if i.val < 4098 then 49 else (if i.val < 4099 then 24 else 21))))) else (if i.val < 4108 then (if i.val < 4104 then (if i.val < 4102 then (if i.val < 4101 then 49 else 57) else (if i.val < 4103 then 49 else 57)) else (if i.val < 4106 then (if i.val < 4105 then 38 else 46) else (if i.val < 4107 then 57 else 46))) else (if i.val < 4112 then (if i.val < 4110 then (if i.val < 4109 then 16 else 66) else (if i.val < 4111 then 73 else 15)) else (if i.val < 4114 then (if i.val < 4113 then 34 else 34) else (if i.val < 4115 then 10 else (if i.val < 4116 then 73 else 66))))))) else (if i.val < 4151 then (if i.val < 4134 then (if i.val < 4125 then (if i.val < 4121 then (if i.val < 4119 then (if i.val < 4118 then 60 else 21) else (if i.val < 4120 then 57 else 10)) else (if i.val < 4123 then (if i.val < 4122 then 38 else 60) else (if i.val < 4124 then 86 else 34))) else (if i.val < 4129 then (if i.val < 4127 then (if i.val < 4126 then 60 else 35) else (if i.val < 4128 then 73 else 10)) else (if i.val < 4131 then (if i.val < 4130 then 21 else 16) else (if i.val < 4132 then 57 else (if i.val < 4133 then 21 else 57))))) else (if i.val < 4142 then (if i.val < 4138 then (if i.val < 4136 then (if i.val < 4135 then 71 else 57) else (if i.val < 4137 then 78 else 46)) else (if i.val < 4140 then (if i.val < 4139 then 60 else 82) else (if i.val < 4141 then 49 else 38))) else (if i.val < 4146 then (if i.val < 4144 then (if i.val < 4143 then 21 else 30) else (if i.val < 4145 then 46 else 57)) else (if i.val < 4148 then (if i.val < 4147 then 40 else 35) else (if i.val < 4149 then 38 else (if i.val < 4150 then 66 else 46)))))) else (if i.val < 4168 then (if i.val < 4159 then (if i.val < 4155 then (if i.val < 4153 then (if i.val < 4152 then 32 else 16) else (if i.val < 4154 then 30 else 49)) else (if i.val < 4157 then (if i.val < 4156 then 30 else 49) else (if i.val < 4158 then 46 else 35))) else (if i.val < 4163 then (if i.val < 4161 then (if i.val < 4160 then 38 else 57) else (if i.val < 4162 then 86 else 38)) else (if i.val < 4165 then (if i.val < 4164 then 69 else 13) else (if i.val < 4166 then 46 else (if i.val < 4167 then 38 else 57))))) else (if i.val < 4176 then (if i.val < 4172 then (if i.val < 4170 then (if i.val < 4169 then 47 else 18) else (if i.val < 4171 then 71 else 46)) else (if i.val < 4174 then (if i.val < 4173 then 13 else 16) else (if i.val < 4175 then 34 else 18))) else (if i.val < 4180 then (if i.val < 4178 then (if i.val < 4177 then 57 else 49) else (if i.val < 4179 then 38 else 32)) else (if i.val < 4182 then (if i.val < 4181 then 46 else 60) else (if i.val < 4183 then 38 else (if i.val < 4184 then 13 else 71)))))))) else (if i.val < 4252 then (if i.val < 4218 then (if i.val < 4201 then (if i.val < 4193 then (if i.val < 4189 then (if i.val < 4187 then (if i.val < 4186 then 38 else 40) else (if i.val < 4188 then 16 else 38)) else (if i.val < 4191 then (if i.val < 4190 then 73 else 49) else (if i.val < 4192 then 16 else 57))) else (if i.val < 4197 then (if i.val < 4195 then (if i.val < 4194 then 38 else 49) else (if i.val < 4196 then 21 else 13)) else (if i.val < 4199 then (if i.val < 4198 then 15 else 21) else (if i.val < 4200 then 40 else 56)))) else (if i.val < 4209 then (if i.val < 4205 then (if i.val < 4203 then (if i.val < 4202 then 16 else 49) else (if i.val < 4204 then 38 else 40)) else (if i.val < 4207 then (if i.val < 4206 then 49 else 69) else (if i.val < 4208 then 40 else 69))) else (if i.val < 4213 then (if i.val < 4211 then (if i.val < 4210 then 38 else 47) else (if i.val < 4212 then 71 else 71)) else (if i.val < 4215 then (if i.val < 4214 then 21 else 38) else (if i.val < 4216 then 26 else (if i.val < 4217 then 40 else 13)))))) else (if i.val < 4235 then (if i.val < 4226 then (if i.val < 4222 then (if i.val < 4220 then (if i.val < 4219 then 45 else 13) else (if i.val < 4221 then 49 else 40)) else (if i.val < 4224 then (if i.val < 4223 then 26 else 49) else (if i.val < 4225 then 15 else 13))) else (if i.val < 4230 then (if i.val < 4228 then (if i.val < 4227 then 21 else 71) else (if i.val < 4229 then 30 else 13)) else (if i.val < 4232 then (if i.val < 4231 then 13 else 26) else (if i.val < 4233 then 69 else (if i.val < 4234 then 49 else 47))))) else (if i.val < 4243 then (if i.val < 4239 then (if i.val < 4237 then (if i.val < 4236 then 30 else 26) else (if i.val < 4238 then 15 else 16)) else (if i.val < 4241 then (if i.val < 4240 then 34 else 49) else (if i.val < 4242 then 45 else 71))) else (if i.val < 4247 then (if i.val < 4245 then (if i.val < 4244 then 75 else 34) else (if i.val < 4246 then 13 else 84)) else (if i.val < 4249 then (if i.val < 4248 then 84 else 24) else (if i.val < 4250 then 40 else (if i.val < 4251 then 40 else 30))))))) else (if i.val < 4286 then (if i.val < 4269 then (if i.val < 4260 then (if i.val < 4256 then (if i.val < 4254 then (if i.val < 4253 then 30 else 15) else (if i.val < 4255 then 26 else 40)) else (if i.val < 4258 then (if i.val < 4257 then 30 else 46) else (if i.val < 4259 then 49 else 49))) else (if i.val < 4264 then (if i.val < 4262 then (if i.val < 4261 then 13 else 30) else (if i.val < 4263 then 73 else 30)) else (if i.val < 4266 then (if i.val < 4265 then 15 else 69) else (if i.val < 4267 then 30 else (if i.val < 4268 then 30 else 49))))) else (if i.val < 4277 then (if i.val < 4273 then (if i.val < 4271 then (if i.val < 4270 then 69 else 84) else (if i.val < 4272 then 26 else 71)) else (if i.val < 4275 then (if i.val < 4274 then 73 else 30) else (if i.val < 4276 then 30 else 21))) else (if i.val < 4281 then (if i.val < 4279 then (if i.val < 4278 then 65 else 40) else (if i.val < 4280 then 60 else 30)) else (if i.val < 4283 then (if i.val < 4282 then 49 else 75) else (if i.val < 4284 then 30 else (if i.val < 4285 then 30 else 30)))))) else (if i.val < 4303 then (if i.val < 4294 then (if i.val < 4290 then (if i.val < 4288 then (if i.val < 4287 then 30 else 57) else (if i.val < 4289 then 30 else 13)) else (if i.val < 4292 then (if i.val < 4291 then 40 else 30) else (if i.val < 4293 then 75 else 73))) else (if i.val < 4298 then (if i.val < 4296 then (if i.val < 4295 then 30 else 65) else (if i.val < 4297 then 78 else 30)) else (if i.val < 4300 then (if i.val < 4299 then 46 else 45) else (if i.val < 4301 then 69 else (if i.val < 4302 then 40 else 26))))) else (if i.val < 4311 then (if i.val < 4307 then (if i.val < 4305 then (if i.val < 4304 then 24 else 30) else (if i.val < 4306 then 65 else 69)) else (if i.val < 4309 then (if i.val < 4308 then 73 else 24) else (if i.val < 4310 then 65 else 30))) else (if i.val < 4315 then (if i.val < 4313 then (if i.val < 4312 then 35 else 46) else (if i.val < 4314 then 46 else 46)) else (if i.val < 4317 then (if i.val < 4316 then 46 else 46) else (if i.val < 4318 then 57 else (if i.val < 4319 then 34 else 34)))))))))))))

def g32p_supplierGroup01_support : Finset (Fin 102) :=
  {0, 4, 6, 10, 11, 13, 15, 16, 18, 21, 22, 24, 26, 30, 32, 34, 35, 37, 38, 40, 45, 46, 47, 49, 56, 57, 60, 65, 66, 69, 71, 73, 75, 78, 82, 84, 86, 92, 96, 97, 99, 101}

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_supplierGroup01_matrix_000 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 0 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 0 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 0 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_000 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 0 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 0 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 0 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_000 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 0 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_001 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 1 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 1 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 1 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_001 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 1 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 1 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 1 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_001 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 1 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_002 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 2 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 2 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 2 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_002 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 2 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 2 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 2 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_002 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 2 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_003 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 3 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 3 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 3 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_003 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 3 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 3 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 3 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_003 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 3 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_004 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 4 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 4 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 4 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_004 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 4 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 4 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 4 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_004 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 4 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_005 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 5 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 5 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 5 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_005 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 5 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 5 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 5 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_005 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 5 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_006 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 6 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 6 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 6 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_006 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 6 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 6 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 6 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_006 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 6 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_007 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 7 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 7 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 7 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_007 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 7 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 7 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 7 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_007 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 7 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_008 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 8 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 8 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 8 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_008 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 8 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 8 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 8 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_008 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 8 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_009 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 9 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 9 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 9 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_009 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 9 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 9 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 9 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_009 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 9 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_010 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 10 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 10 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 10 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_010 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 10 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 10 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 10 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_010 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 10 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_011 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 11 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 11 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 11 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_011 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 11 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 11 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 11 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_011 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 11 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_012 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 12 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 12 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 12 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_012 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 12 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 12 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 12 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_012 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 12 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_013 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 13 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 13 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 13 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_013 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 13 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 13 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 13 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_013 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 13 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_014 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 14 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 14 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 14 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_014 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 14 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 14 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 14 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_014 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 14 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_015 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 15 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 15 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 15 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_015 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 15 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 15 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 15 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_015 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 15 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_016 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 16 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 16 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 16 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_016 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 16 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 16 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 16 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_016 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 16 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_017 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 17 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 17 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 17 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_017 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 17 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 17 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 17 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_017 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 17 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_018 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 18 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 18 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 18 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_018 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 18 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 18 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 18 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_018 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 18 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_019 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 19 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 19 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 19 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_019 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 19 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 19 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 19 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_019 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 19 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_020 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 20 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 20 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 20 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_020 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 20 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 20 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 20 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_020 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 20 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_021 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 21 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 21 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 21 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_021 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 21 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 21 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 21 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_021 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 21 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_022 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 22 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 22 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 22 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_022 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 22 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 22 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 22 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_022 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 22 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_023 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 23 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 23 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 23 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_023 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 23 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 23 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 23 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_023 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 23 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_024 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 24 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 24 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 24 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_024 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 24 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 24 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 24 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_024 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 24 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_025 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 25 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 25 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 25 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_025 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 25 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 25 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 25 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_025 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 25 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_026 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 26 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 26 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 26 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_026 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 26 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 26 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 26 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_026 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 26 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_027 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 27 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 27 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 27 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_027 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 27 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 27 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 27 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_027 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 27 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_028 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 28 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 28 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 28 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_028 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 28 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 28 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 28 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_028 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 28 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_029 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 29 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 29 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 29 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_029 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 29 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 29 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 29 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_029 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 29 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_030 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 30 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 30 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 30 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_030 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 30 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 30 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 30 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_030 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 30 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_031 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 31 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 31 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 31 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_031 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 31 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 31 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 31 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_031 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 31 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_032 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 32 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 32 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 32 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_032 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 32 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 32 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 32 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_032 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 32 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_033 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 33 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 33 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 33 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_033 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 33 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 33 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 33 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_033 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 33 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_034 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 34 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 34 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 34 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_034 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 34 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 34 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 34 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_034 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 34 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_035 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 35 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 35 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 35 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_035 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 35 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 35 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 35 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_035 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 35 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_036 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 36 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 36 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 36 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_036 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 36 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 36 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 36 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_036 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 36 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_037 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 37 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 37 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 37 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_037 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 37 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 37 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 37 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_037 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 37 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_038 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 38 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 38 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 38 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_038 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 38 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 38 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 38 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_038 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 38 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_039 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 39 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 39 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 39 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_039 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 39 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 39 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 39 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_039 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 39 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_040 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 40 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 40 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 40 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_040 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 40 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 40 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 40 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_040 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 40 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_041 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 41 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 41 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 41 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_041 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 41 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 41 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 41 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_041 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 41 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_042 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 42 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 42 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 42 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_042 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 42 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 42 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 42 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_042 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 42 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_043 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 43 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 43 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 43 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_043 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 43 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 43 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 43 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_043 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 43 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_044 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 44 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 44 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 44 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_044 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 44 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 44 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 44 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_044 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 44 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_045 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 45 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 45 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 45 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_045 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 45 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 45 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 45 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_045 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 45 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_046 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 46 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 46 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 46 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_046 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 46 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 46 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 46 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_046 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 46 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_047 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 47 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 47 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 47 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_047 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 47 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 47 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 47 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_047 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 47 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_048 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 48 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 48 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 48 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_048 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 48 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 48 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 48 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_048 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 48 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_049 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 49 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 49 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 49 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_049 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 49 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 49 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 49 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_049 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 49 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_050 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 50 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 50 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 50 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_050 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 50 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 50 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 50 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_050 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 50 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_051 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 51 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 51 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 51 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_051 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 51 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 51 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 51 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_051 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 51 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_052 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 52 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 52 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 52 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_052 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 52 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 52 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 52 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_052 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 52 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_053 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 53 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 53 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 53 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_053 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 53 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 53 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 53 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_053 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 53 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_054 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 54 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 54 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 54 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_054 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 54 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 54 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 54 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_054 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 54 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_055 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 55 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 55 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 55 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_055 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 55 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 55 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 55 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_055 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 55 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_056 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 56 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 56 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 56 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_056 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 56 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 56 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 56 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_056 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 56 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_057 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 57 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 57 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 57 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_057 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 57 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 57 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 57 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_057 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 57 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_058 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 58 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 58 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 58 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_058 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 58 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 58 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 58 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_058 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 58 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_059 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 59 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 59 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 59 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_059 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 59 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 59 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 59 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_059 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 59 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_060 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 60 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 60 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 60 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_060 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 60 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 60 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 60 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_060 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 60 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_061 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 61 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 61 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 61 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_061 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 61 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 61 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 61 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_061 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 61 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_062 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 62 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 62 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 62 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_062 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 62 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 62 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 62 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_062 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 62 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_063 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 63 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 63 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 63 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_063 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 63 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 63 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 63 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_063 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 63 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_064 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 64 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 64 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 64 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_064 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 64 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 64 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 64 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_064 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 64 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_065 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 65 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 65 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 65 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_065 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 65 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 65 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 65 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_065 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 65 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_066 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 66 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 66 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 66 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_066 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 66 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 66 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 66 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_066 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 66 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_067 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 67 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 67 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 67 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_067 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 67 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 67 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 67 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_067 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 67 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_068 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 68 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 68 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 68 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_068 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 68 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 68 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 68 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_068 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 68 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_069 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 69 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 69 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 69 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_069 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 69 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 69 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 69 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_069 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 69 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_070 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 70 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 70 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 70 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_070 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 70 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 70 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 70 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_070 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 70 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_071 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 71 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 71 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 71 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_071 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 71 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 71 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 71 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_071 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 71 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_072 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 72 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 72 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 72 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_072 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 72 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 72 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 72 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_072 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 72 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_073 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 73 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 73 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 73 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_073 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 73 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 73 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 73 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_073 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 73 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_074 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 74 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 74 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 74 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_074 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 74 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 74 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 74 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_074 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 74 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_075 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 75 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 75 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 75 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_075 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 75 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 75 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 75 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_075 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 75 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_076 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 76 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 76 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 76 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_076 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 76 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 76 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 76 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_076 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 76 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_077 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 77 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 77 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 77 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_077 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 77 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 77 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 77 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_077 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 77 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_078 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 78 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 78 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 78 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_078 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 78 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 78 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 78 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_078 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 78 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_079 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 79 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 79 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 79 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_079 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 79 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 79 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 79 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_079 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 79 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_080 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 80 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 80 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 80 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_080 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 80 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 80 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 80 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_080 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 80 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_081 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 81 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 81 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 81 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_081 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 81 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 81 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 81 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_081 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 81 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_082 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 82 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 82 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 82 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_082 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 82 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 82 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 82 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_082 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 82 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_083 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 83 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 83 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 83 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_083 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 83 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 83 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 83 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_083 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 83 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_084 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 84 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 84 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 84 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_084 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 84 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 84 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 84 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_084 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 84 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_085 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 85 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 85 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 85 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_085 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 85 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 85 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 85 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_085 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 85 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_086 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 86 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 86 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 86 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_086 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 86 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 86 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 86 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_086 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 86 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_087 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 87 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 87 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 87 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_087 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 87 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 87 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 87 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_087 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 87 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_088 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 88 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 88 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 88 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_088 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 88 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 88 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 88 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_088 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 88 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_089 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 89 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 89 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 89 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_089 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 89 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 89 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 89 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_089 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 89 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_090 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 90 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 90 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 90 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_090 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 90 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 90 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 90 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_090 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 90 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_091 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 91 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 91 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 91 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_091 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 91 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 91 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 91 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_091 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 91 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_092 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 92 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 92 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 92 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_092 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 92 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 92 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 92 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_092 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 92 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_093 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 93 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 93 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 93 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_093 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 93 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 93 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 93 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_093 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 93 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_094 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 94 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 94 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 94 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_094 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 94 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 94 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 94 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_094 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 94 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_095 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 95 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 95 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 95 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_095 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 95 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 95 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 95 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_095 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 95 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_096 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 96 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 96 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 96 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_096 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 96 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 96 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 96 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_096 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 96 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_097 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 97 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 97 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 97 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_097 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 97 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 97 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 97 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_097 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 97 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_098 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 98 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 98 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 98 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_098 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 98 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 98 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 98 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_098 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 98 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_099 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 99 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 99 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 99 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_099 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 99 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 99 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 99 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_099 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 99 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_100 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 100 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 100 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 100 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_100 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 100 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 100 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 100 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_100 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 100 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_101 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 101 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 101 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 101 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_101 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 101 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 101 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 101 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_101 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 101 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_102 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 102 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 102 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 102 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_102 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 102 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 102 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 102 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_102 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 102 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_103 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 103 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 103 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 103 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_103 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 103 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 103 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 103 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_103 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 103 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_104 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 104 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 104 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 104 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_104 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 104 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 104 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 104 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_104 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 104 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_105 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 105 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 105 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 105 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_105 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 105 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 105 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 105 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_105 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 105 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_106 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 106 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 106 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 106 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_106 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 106 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 106 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 106 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_106 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 106 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_107 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 107 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 107 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 107 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_107 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 107 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 107 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 107 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_107 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 107 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_108 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 108 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 108 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 108 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_108 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 108 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 108 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 108 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_108 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 108 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_109 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 109 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 109 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 109 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_109 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 109 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 109 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 109 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_109 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 109 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_110 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 110 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 110 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 110 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_110 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 110 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 110 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 110 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_110 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 110 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_111 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 111 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 111 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 111 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_111 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 111 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 111 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 111 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_111 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 111 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_112 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 112 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 112 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 112 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_112 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 112 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 112 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 112 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_112 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 112 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_113 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 113 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 113 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 113 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_113 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 113 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 113 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 113 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_113 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 113 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_114 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 114 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 114 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 114 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_114 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 114 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 114 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 114 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_114 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 114 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_115 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 115 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 115 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 115 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_115 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 115 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 115 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 115 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_115 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 115 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_116 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 116 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 116 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 116 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_116 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 116 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 116 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 116 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_116 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 116 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_117 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 117 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 117 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 117 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_117 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 117 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 117 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 117 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_117 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 117 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_118 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 118 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 118 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 118 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_118 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 118 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 118 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 118 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_118 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 118 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_119 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 119 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 119 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 119 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_119 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 119 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 119 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 119 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_119 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 119 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_120 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 120 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 120 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 120 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_120 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 120 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 120 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 120 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_120 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 120 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_121 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 121 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 121 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 121 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_121 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 121 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 121 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 121 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_121 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 121 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_122 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 122 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 122 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 122 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_122 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 122 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 122 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 122 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_122 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 122 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_123 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 123 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 123 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 123 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_123 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 123 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 123 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 123 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_123 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 123 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_124 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 124 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 124 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 124 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_124 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 124 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 124 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 124 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_124 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 124 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_125 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 125 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 125 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 125 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_125 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 125 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 125 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 125 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_125 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 125 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_126 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 126 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 126 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 126 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_126 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 126 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 126 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 126 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_126 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 126 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_127 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 127 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 127 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 127 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_127 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 127 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 127 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 127 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_127 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 127 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_128 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 128 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 128 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 128 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_128 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 128 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 128 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 128 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_128 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 128 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_129 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 129 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 129 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 129 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_129 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 129 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 129 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 129 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_129 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 129 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_130 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 130 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 130 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 130 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_130 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 130 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 130 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 130 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_130 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 130 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_131 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 131 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 131 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 131 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_131 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 131 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 131 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 131 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_131 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 131 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_132 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 132 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 132 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 132 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_132 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 132 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 132 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 132 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_132 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 132 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_133 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 133 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 133 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 133 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_133 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 133 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 133 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 133 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_133 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 133 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_134 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 134 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 134 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 134 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_134 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 134 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 134 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 134 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_134 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 134 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_135 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 135 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 135 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 135 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_135 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 135 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 135 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 135 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_135 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 135 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_136 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 136 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 136 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 136 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_136 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 136 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 136 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 136 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_136 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 136 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_137 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 137 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 137 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 137 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_137 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 137 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 137 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 137 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_137 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 137 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_138 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 138 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 138 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 138 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_138 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 138 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 138 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 138 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_138 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 138 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_139 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 139 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 139 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 139 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_139 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 139 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 139 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 139 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_139 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 139 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_140 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 140 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 140 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 140 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_140 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 140 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 140 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 140 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_140 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 140 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_141 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 141 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 141 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 141 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_141 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 141 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 141 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 141 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_141 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 141 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_142 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 142 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 142 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 142 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_142 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 142 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 142 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 142 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_142 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 142 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_143 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 143 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 143 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 143 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_143 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 143 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 143 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 143 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_143 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 143 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_144 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 144 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 144 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 144 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_144 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 144 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 144 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 144 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_144 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 144 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_145 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 145 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 145 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 145 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_145 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 145 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 145 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 145 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_145 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 145 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_146 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 146 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 146 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 146 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_146 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 146 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 146 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 146 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_146 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 146 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_147 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 147 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 147 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 147 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_147 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 147 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 147 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 147 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_147 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 147 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_148 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 148 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 148 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 148 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_148 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 148 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 148 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 148 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_148 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 148 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_149 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 149 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 149 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 149 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_149 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 149 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 149 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 149 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_149 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 149 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_150 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 150 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 150 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 150 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_150 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 150 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 150 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 150 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_150 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 150 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_151 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 151 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 151 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 151 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_151 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 151 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 151 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 151 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_151 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 151 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_152 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 152 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 152 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 152 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_152 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 152 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 152 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 152 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_152 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 152 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_153 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 153 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 153 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 153 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_153 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 153 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 153 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 153 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_153 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 153 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_154 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 154 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 154 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 154 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_154 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 154 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 154 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 154 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_154 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 154 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_155 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 155 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 155 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 155 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_155 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 155 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 155 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 155 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_155 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 155 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_156 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 156 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 156 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 156 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_156 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 156 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 156 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 156 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_156 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 156 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_157 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 157 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 157 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 157 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_157 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 157 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 157 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 157 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_157 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 157 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_158 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 158 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 158 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 158 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_158 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 158 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 158 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 158 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_158 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 158 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_159 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 159 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 159 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 159 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_159 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 159 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 159 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 159 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_159 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 159 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_160 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 160 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 160 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 160 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_160 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 160 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 160 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 160 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_160 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 160 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_161 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 161 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 161 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 161 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_161 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 161 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 161 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 161 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_161 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 161 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_162 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 162 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 162 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 162 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_162 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 162 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 162 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 162 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_162 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 162 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_163 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 163 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 163 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 163 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_163 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 163 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 163 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 163 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_163 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 163 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_164 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 164 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 164 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 164 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_164 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 164 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 164 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 164 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_164 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 164 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_165 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 165 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 165 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 165 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_165 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 165 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 165 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 165 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_165 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 165 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_166 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 166 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 166 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 166 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_166 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 166 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 166 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 166 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_166 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 166 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_167 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 167 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 167 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 167 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_167 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 167 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 167 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 167 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_167 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 167 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_168 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 168 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 168 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 168 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_168 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 168 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 168 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 168 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_168 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 168 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_169 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 169 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 169 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 169 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_169 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 169 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 169 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 169 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_169 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 169 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_170 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 170 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 170 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 170 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_170 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 170 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 170 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 170 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_170 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 170 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_171 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 171 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 171 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 171 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_171 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 171 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 171 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 171 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_171 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 171 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_172 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 172 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 172 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 172 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_172 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 172 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 172 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 172 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_172 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 172 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_173 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 173 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 173 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 173 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_173 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 173 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 173 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 173 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_173 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 173 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_174 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 174 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 174 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 174 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_174 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 174 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 174 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 174 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_174 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 174 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_175 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 175 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 175 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 175 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_175 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 175 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 175 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 175 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_175 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 175 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_176 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 176 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 176 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 176 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_176 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 176 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 176 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 176 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_176 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 176 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_177 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 177 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 177 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 177 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_177 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 177 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 177 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 177 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_177 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 177 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_178 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 178 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 178 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 178 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_178 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 178 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 178 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 178 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_178 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 178 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_179 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 179 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 179 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 179 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_179 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 179 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 179 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 179 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_179 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 179 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_180 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 180 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 180 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 180 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_180 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 180 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 180 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 180 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_180 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 180 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_181 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 181 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 181 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 181 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_181 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 181 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 181 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 181 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_181 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 181 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_182 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 182 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 182 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 182 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_182 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 182 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 182 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 182 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_182 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 182 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_183 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 183 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 183 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 183 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_183 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 183 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 183 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 183 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_183 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 183 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_184 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 184 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 184 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 184 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_184 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 184 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 184 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 184 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_184 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 184 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_185 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 185 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 185 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 185 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_185 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 185 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 185 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 185 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_185 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 185 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_186 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 186 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 186 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 186 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_186 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 186 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 186 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 186 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_186 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 186 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_187 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 187 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 187 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 187 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_187 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 187 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 187 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 187 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_187 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 187 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_188 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 188 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 188 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 188 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_188 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 188 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 188 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 188 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_188 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 188 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_189 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 189 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 189 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 189 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_189 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 189 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 189 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 189 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_189 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 189 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_190 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 190 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 190 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 190 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_190 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 190 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 190 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 190 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_190 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 190 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_191 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 191 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 191 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 191 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_191 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 191 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 191 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 191 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_191 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 191 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_192 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 192 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 192 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 192 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_192 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 192 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 192 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 192 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_192 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 192 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_193 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 193 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 193 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 193 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_193 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 193 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 193 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 193 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_193 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 193 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_194 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 194 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 194 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 194 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_194 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 194 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 194 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 194 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_194 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 194 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_195 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 195 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 195 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 195 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_195 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 195 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 195 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 195 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_195 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 195 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_196 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 196 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 196 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 196 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_196 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 196 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 196 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 196 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_196 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 196 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_197 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 197 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 197 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 197 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_197 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 197 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 197 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 197 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_197 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 197 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_198 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 198 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 198 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 198 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_198 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 198 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 198 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 198 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_198 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 198 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_199 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 199 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 199 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 199 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_199 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 199 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 199 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 199 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_199 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 199 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_200 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 200 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 200 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 200 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_200 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 200 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 200 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 200 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_200 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 200 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_201 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 201 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 201 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 201 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_201 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 201 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 201 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 201 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_201 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 201 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_202 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 202 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 202 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 202 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_202 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 202 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 202 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 202 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_202 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 202 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_203 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 203 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 203 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 203 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_203 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 203 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 203 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 203 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_203 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 203 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_204 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 204 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 204 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 204 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_204 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 204 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 204 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 204 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_204 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 204 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_205 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 205 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 205 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 205 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_205 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 205 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 205 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 205 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_205 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 205 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_206 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 206 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 206 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 206 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_206 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 206 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 206 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 206 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_206 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 206 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_207 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 207 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 207 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 207 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_207 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 207 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 207 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 207 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_207 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 207 r) ∈ g32p_supplierGroup01_support := by
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

theorem g32p_supplierGroup01_matrix_208 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 208 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 208 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 208 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_208 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 208 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 208 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 208 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_208 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 208 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_209 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 209 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 209 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 209 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_209 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 209 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 209 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 209 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_209 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 209 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_210 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 210 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 210 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 210 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_210 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 210 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 210 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 210 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_210 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 210 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_211 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 211 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 211 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 211 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_211 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 211 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 211 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 211 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_211 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 211 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_212 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 212 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 212 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 212 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_212 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 212 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 212 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 212 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_212 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 212 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_213 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 213 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 213 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 213 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_213 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 213 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 213 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 213 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_213 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 213 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_214 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 214 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 214 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 214 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_214 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 214 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 214 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 214 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_214 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 214 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_215 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 215 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 215 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 215 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_215 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 215 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 215 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 215 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_215 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 215 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_216 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 216 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 216 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 216 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_216 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 216 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 216 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 216 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_216 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 216 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_217 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 217 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 217 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 217 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_217 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 217 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 217 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 217 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_217 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 217 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_218 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 218 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 218 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 218 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_218 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 218 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 218 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 218 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_218 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 218 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_219 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 219 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 219 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 219 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_219 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 219 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 219 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 219 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_219 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 219 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_220 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 220 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 220 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 220 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_220 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 220 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 220 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 220 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_220 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 220 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_221 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 221 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 221 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 221 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_221 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 221 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 221 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 221 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_221 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 221 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_222 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 222 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 222 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 222 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_222 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 222 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 222 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 222 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_222 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 222 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

theorem g32p_supplierGroup01_matrix_223 : ∀ r : Fin 16,
    g32p_row03_groupNodes (g32p_finBlockIndex 4320 223 r) =
      g32p_supplierForest_nodes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 223 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 223 r)).2 := by
  decide +kernel

theorem g32p_supplierGroup01_class_223 : ∀ r : Fin 16,
    g32p_supplierForest_classes (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 223 r)).1 (g32p_supplierGroup01_source (g32p_finBlockIndex 4320 223 r)).2 =
      g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 223 r) := by
  decide +kernel

theorem g32p_supplierGroup01_support_223 : ∀ r : Fin 16,
    g32p_supplierGroup01_classify (g32p_finBlockIndex 4320 223 r) ∈ g32p_supplierGroup01_support := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
