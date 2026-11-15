import HodgeLean.Foundations.Program.G32PropFourSixPacked0227
import HodgeLean.Foundations.Program.G32PropFourSixPacked0228
import HodgeLean.Foundations.Program.G32PropFourSixPacked0229
import HodgeLean.Foundations.Program.G32PropFourSixPacked0230
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0217
import HodgeLean.Foundations.Program.G32PropFourSixPacked0218
import HodgeLean.Foundations.Program.G32PropFourSixPacked0220
import HodgeLean.Foundations.Program.G32PropFourSixPacked0221
import HodgeLean.Foundations.Program.G32PropFourSixPacked0225

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_032 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_001543 else g32p_supplierForest_node_001557) else (if i.val < 3 then g32p_supplierForest_node_001611 else g32p_supplierForest_node_001622)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_001628 else g32p_supplierForest_node_001643) else (if i.val < 7 then g32p_supplierForest_node_001682 else g32p_supplierForest_node_001810))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_001843 else g32p_supplierForest_node_001872) else (if i.val < 11 then g32p_supplierForest_node_001877 else g32p_supplierForest_node_001880)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_001911 else g32p_supplierForest_node_001990) else (if i.val < 15 then g32p_supplierForest_node_002030 else g32p_supplierForest_node_002055)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_002105 else g32p_supplierForest_node_002129) else (if i.val < 19 then g32p_supplierForest_node_002152 else g32p_supplierForest_node_002294)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_002329 else g32p_supplierForest_node_002373) else (if i.val < 23 then g32p_supplierForest_node_002393 else g32p_supplierForest_node_002396))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_002482 else g32p_supplierForest_node_002515) else (if i.val < 27 then g32p_supplierForest_node_002525 else g32p_supplierForest_node_002578)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_002636 else g32p_supplierForest_node_002684) else (if i.val < 31 then g32p_supplierForest_node_002714 else g32p_supplierForest_node_002756))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_002810 else g32p_supplierForest_node_002822) else (if i.val < 35 then g32p_supplierForest_node_002855 else g32p_supplierForest_node_002869)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_002895 else g32p_supplierForest_node_002990) else (if i.val < 39 then g32p_supplierForest_node_003009 else g32p_supplierForest_node_003013))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_003016 else g32p_supplierForest_node_003031) else (if i.val < 43 then g32p_supplierForest_node_003065 else g32p_supplierForest_node_003069)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_003085 else g32p_supplierForest_node_003100) else (if i.val < 47 then g32p_supplierForest_node_003111 else g32p_supplierForest_node_003116)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_003120 else g32p_supplierForest_node_003144) else (if i.val < 51 then g32p_supplierForest_node_003148 else g32p_supplierForest_node_003174)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_003182 else g32p_supplierForest_node_003184) else (if i.val < 55 then g32p_supplierForest_node_003208 else g32p_supplierForest_node_003239))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_003264 else g32p_supplierForest_node_003278) else (if i.val < 59 then g32p_supplierForest_node_003300 else g32p_supplierForest_node_003319)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_003372 else g32p_supplierForest_node_003393) else (if i.val < 63 then g32p_supplierForest_node_003406 else g32p_supplierForest_node_003409)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_003413 else g32p_supplierForest_node_003423) else (if i.val < 67 then g32p_supplierForest_node_003456 else g32p_supplierForest_node_003467)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_003475 else g32p_supplierForest_node_003566) else (if i.val < 71 then g32p_supplierForest_node_003570 else g32p_supplierForest_node_003599))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_003600 else g32p_supplierForest_node_003655) else (if i.val < 75 then g32p_supplierForest_node_003657 else g32p_supplierForest_node_003668)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_003679 else g32p_supplierForest_node_003717) else (if i.val < 79 then g32p_supplierForest_node_003768 else g32p_supplierForest_node_003821)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_003827 else g32p_supplierForest_node_003836) else (if i.val < 83 then g32p_supplierForest_node_003840 else g32p_supplierForest_node_003851)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_003854 else g32p_supplierForest_node_003861) else (if i.val < 87 then g32p_supplierForest_node_003868 else g32p_supplierForest_node_003882))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_003883 else g32p_supplierForest_node_003924) else (if i.val < 91 then g32p_supplierForest_node_003984 else g32p_supplierForest_node_004033)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_004066 else g32p_supplierForest_node_004070) else (if i.val < 95 then g32p_supplierForest_node_004085 else g32p_supplierForest_node_004147))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_004235 else g32p_supplierForest_node_004300) else (if i.val < 99 then g32p_supplierForest_node_004335 else g32p_supplierForest_node_004366)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_004377 else g32p_supplierForest_node_004382) else (if i.val < 103 then g32p_supplierForest_node_004404 else g32p_supplierForest_node_004461))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_004508 else g32p_supplierForest_node_004521) else (if i.val < 107 then g32p_supplierForest_node_004550 else g32p_supplierForest_node_004582)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_004595 else g32p_supplierForest_node_004614) else (if i.val < 111 then g32p_supplierForest_node_004664 else g32p_supplierForest_node_004715)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_004751 else g32p_supplierForest_node_004762) else (if i.val < 115 then g32p_supplierForest_node_004780 else g32p_supplierForest_node_004807)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_004838 else g32p_supplierForest_node_004866) else (if i.val < 119 then g32p_supplierForest_node_004869 else g32p_supplierForest_node_004879))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_004889 else g32p_supplierForest_node_004945) else (if i.val < 123 then g32p_supplierForest_node_004967 else g32p_supplierForest_node_004970)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_004980 else g32p_supplierForest_node_004990) else (if i.val < 127 then g32p_supplierForest_node_004991 else g32p_supplierForest_node_005067))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_005175 else g32p_supplierForest_node_005254) else (if i.val < 131 then g32p_supplierForest_node_005255 else g32p_supplierForest_node_005261)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_005265 else g32p_supplierForest_node_005311) else (if i.val < 135 then g32p_supplierForest_node_005383 else g32p_supplierForest_node_005387))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_005436 else g32p_supplierForest_node_005487) else (if i.val < 139 then g32p_supplierForest_node_005498 else g32p_supplierForest_node_005524)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_005528 else g32p_supplierForest_node_005559) else (if i.val < 143 then g32p_supplierForest_node_005601 else g32p_supplierForest_node_005673)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_005729 else g32p_supplierForest_node_005793) else (if i.val < 147 then g32p_supplierForest_node_005796 else g32p_supplierForest_node_005799)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_005835 else g32p_supplierForest_node_005864) else (if i.val < 151 then g32p_supplierForest_node_005911 else g32p_supplierForest_node_005912))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_005923 else g32p_supplierForest_node_005931) else (if i.val < 155 then g32p_supplierForest_node_005963 else g32p_supplierForest_node_005984)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_005993 else g32p_supplierForest_node_006002) else (if i.val < 159 then g32p_supplierForest_node_006059 else g32p_supplierForest_node_006071))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_006077 else g32p_supplierForest_node_006098) else (if i.val < 163 then g32p_supplierForest_node_006102 else g32p_supplierForest_node_006137)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_006146 else g32p_supplierForest_node_006167) else (if i.val < 167 then g32p_supplierForest_node_006200 else g32p_supplierForest_node_006235))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_006270 else g32p_supplierForest_node_006271) else (if i.val < 171 then g32p_supplierForest_node_006289 else g32p_supplierForest_node_006356)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_006383 else g32p_supplierForest_node_006388) else (if i.val < 175 then g32p_supplierForest_node_006407 else g32p_supplierForest_node_006413)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_006418 else g32p_supplierForest_node_006446) else (if i.val < 179 then g32p_supplierForest_node_006454 else g32p_supplierForest_node_006517)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_006524 else g32p_supplierForest_node_006569) else (if i.val < 183 then g32p_supplierForest_node_006572 else g32p_supplierForest_node_006587))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_006599 else g32p_supplierForest_node_006675) else (if i.val < 187 then g32p_supplierForest_node_006750 else g32p_supplierForest_node_006785)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_006807 else g32p_supplierForest_node_006855) else (if i.val < 191 then g32p_supplierForest_node_006865 else g32p_supplierForest_node_006874)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_006911 else g32p_supplierForest_node_006986) else (if i.val < 195 then g32p_supplierForest_node_007004 else g32p_supplierForest_node_007033)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_007037 else g32p_supplierForest_node_007043) else (if i.val < 199 then g32p_supplierForest_node_007067 else g32p_supplierForest_node_007090))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_007126 else g32p_supplierForest_node_007149) else (if i.val < 203 then g32p_supplierForest_node_007155 else g32p_supplierForest_node_007170)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_007183 else g32p_supplierForest_node_007237) else (if i.val < 207 then g32p_supplierForest_node_007239 else g32p_supplierForest_node_007250)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_007271 else g32p_supplierForest_node_007283) else (if i.val < 211 then g32p_supplierForest_node_007299 else g32p_supplierForest_node_007306)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_007399 else g32p_supplierForest_node_007426) else (if i.val < 215 then g32p_supplierForest_node_007472 else g32p_supplierForest_node_007490))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_007704 else g32p_supplierForest_node_007755) else (if i.val < 219 then g32p_supplierForest_node_007760 else g32p_supplierForest_node_007800)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_007810 else g32p_supplierForest_node_007861) else (if i.val < 223 then g32p_supplierForest_node_007897 else g32p_supplierForest_node_007930))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_007936 else g32p_supplierForest_node_007960) else (if i.val < 227 then g32p_supplierForest_node_008007 else g32p_supplierForest_node_008026)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_008030 else g32p_supplierForest_node_008044) else (if i.val < 231 then g32p_supplierForest_node_008047 else g32p_supplierForest_node_008066))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_008078 else g32p_supplierForest_node_008080) else (if i.val < 235 then g32p_supplierForest_node_008083 else g32p_supplierForest_node_008086)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_008107 else g32p_supplierForest_node_008109) else (if i.val < 239 then g32p_supplierForest_node_008114 else g32p_supplierForest_node_008131)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_008146 else g32p_supplierForest_node_008156) else (if i.val < 243 then g32p_supplierForest_node_008180 else g32p_supplierForest_node_008185)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_008248 else g32p_supplierForest_node_008338) else (if i.val < 247 then g32p_supplierForest_node_008340 else g32p_supplierForest_node_008363))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_008366 else g32p_supplierForest_node_008401) else (if i.val < 251 then g32p_supplierForest_node_008417 else g32p_supplierForest_node_008441)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_008461 else g32p_supplierForest_node_008489) else (if i.val < 255 then g32p_supplierForest_node_008493 else g32p_supplierForest_node_008505))))))))

def g32p_supplierForest_classes_032 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 10 else 9) else (if i.val < 3 then 13 else 27)) else (if i.val < 6 then (if i.val < 5 then 10 else 13) else (if i.val < 7 then 10 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 25 else 26) else (if i.val < 11 then 10 else 1)) else (if i.val < 14 then (if i.val < 13 then 8 else 13) else (if i.val < 15 then 10 else 10)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 10 else 10) else (if i.val < 19 then 27 else 8)) else (if i.val < 22 then (if i.val < 21 then 28 else 27) else (if i.val < 23 then 27 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 10 else 26) else (if i.val < 27 then 9 else 14)) else (if i.val < 30 then (if i.val < 29 then 15 else 15) else (if i.val < 31 then 15 else 17))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 16 else 3) else (if i.val < 35 then 3 else 16)) else (if i.val < 38 then (if i.val < 37 then 16 else 31) else (if i.val < 39 then 14 else 32))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 30 else 4) else (if i.val < 43 then 17 else 31)) else (if i.val < 46 then (if i.val < 45 then 15 else 15) else (if i.val < 47 then 17 else 17)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 15 else 3) else (if i.val < 51 then 16 else 17)) else (if i.val < 54 then (if i.val < 53 then 4 else 15) else (if i.val < 55 then 4 else 14))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 31 else 14) else (if i.val < 59 then 15 else 4)) else (if i.val < 62 then (if i.val < 61 then 31 else 34) else (if i.val < 63 then 16 else 31)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 15 else 17) else (if i.val < 67 then 34 else 31)) else (if i.val < 70 then (if i.val < 69 then 16 else 3) else (if i.val < 71 then 15 else 17))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 3 else 3) else (if i.val < 75 then 15 else 34)) else (if i.val < 78 then (if i.val < 77 then 3 else 14) else (if i.val < 79 then 31 else 16)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 17 else 17) else (if i.val < 83 then 17 else 14)) else (if i.val < 86 then (if i.val < 85 then 29 else 14) else (if i.val < 87 then 14 else 15))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 34 else 3) else (if i.val < 91 then 32 else 4)) else (if i.val < 94 then (if i.val < 93 then 32 else 3) else (if i.val < 95 then 31 else 15))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 4 else 30) else (if i.val < 99 then 3 else 3)) else (if i.val < 102 then (if i.val < 101 then 2 else 14) else (if i.val < 103 then 3 else 4))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 30 else 14) else (if i.val < 107 then 31 else 30)) else (if i.val < 110 then (if i.val < 109 then 33 else 15) else (if i.val < 111 then 14 else 14)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 30 else 16) else (if i.val < 115 then 17 else 15)) else (if i.val < 118 then (if i.val < 117 then 15 else 16) else (if i.val < 119 then 30 else 17))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 4 else 34) else (if i.val < 123 then 16 else 31)) else (if i.val < 126 then (if i.val < 125 then 14 else 4) else (if i.val < 127 then 32 else 15))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 16 else 17) else (if i.val < 131 then 16 else 4)) else (if i.val < 134 then (if i.val < 133 then 31 else 14) else (if i.val < 135 then 30 else 34))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 30 else 17) else (if i.val < 139 then 16 else 4)) else (if i.val < 142 then (if i.val < 141 then 31 else 32) else (if i.val < 143 then 32 else 15)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 14 else 20) else (if i.val < 147 then 24 else 19)) else (if i.val < 150 then (if i.val < 149 then 19 else 7) else (if i.val < 151 then 22 else 21))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 7 else 22) else (if i.val < 155 then 5 else 23)) else (if i.val < 158 then (if i.val < 157 then 22 else 6) else (if i.val < 159 then 7 else 22))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 21 else 5) else (if i.val < 163 then 21 else 21)) else (if i.val < 166 then (if i.val < 165 then 5 else 22) else (if i.val < 167 then 7 else 5))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 22 else 22) else (if i.val < 171 then 23 else 5)) else (if i.val < 174 then (if i.val < 173 then 19 else 18) else (if i.val < 175 then 18 else 5)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 22 else 24) else (if i.val < 179 then 19 else 22)) else (if i.val < 182 then (if i.val < 181 then 24 else 22) else (if i.val < 183 then 24 else 6))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 22 else 7) else (if i.val < 187 then 24 else 39)) else (if i.val < 190 then (if i.val < 189 then 39 else 7) else (if i.val < 191 then 21 else 40)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 19 else 22) else (if i.val < 195 then 22 else 24)) else (if i.val < 198 then (if i.val < 197 then 23 else 22) else (if i.val < 199 then 22 else 7))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 5 else 5) else (if i.val < 203 then 5 else 22)) else (if i.val < 206 then (if i.val < 205 then 21 else 22) else (if i.val < 207 then 7 else 20)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 7 else 19) else (if i.val < 211 then 39 else 6)) else (if i.val < 214 then (if i.val < 213 then 38 else 5) else (if i.val < 215 then 21 else 40))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 24 else 20) else (if i.val < 219 then 22 else 21)) else (if i.val < 222 then (if i.val < 221 then 40 else 44) else (if i.val < 223 then 5 else 22))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 22 else 40) else (if i.val < 227 then 5 else 6)) else (if i.val < 230 then (if i.val < 229 then 7 else 23) else (if i.val < 231 then 5 else 19))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 7 else 22) else (if i.val < 235 then 5 else 40)) else (if i.val < 238 then (if i.val < 237 then 24 else 38) else (if i.val < 239 then 40 else 22)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 40 else 7) else (if i.val < 243 then 7 else 5)) else (if i.val < 246 then (if i.val < 245 then 24 else 40) else (if i.val < 247 then 19 else 39))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 40 else 24) else (if i.val < 251 then 40 else 22)) else (if i.val < 254 then (if i.val < 253 then 24 else 20) else (if i.val < 255 then 5 else 22))))))))

theorem g32p_supplierForest_actual_032 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_032 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_032 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_001543
  · exact g32p_supplierForest_actual_001557
  · exact g32p_supplierForest_actual_001611
  · exact g32p_supplierForest_actual_001622
  · exact g32p_supplierForest_actual_001628
  · exact g32p_supplierForest_actual_001643
  · exact g32p_supplierForest_actual_001682
  · exact g32p_supplierForest_actual_001810
  · exact g32p_supplierForest_actual_001843
  · exact g32p_supplierForest_actual_001872
  · exact g32p_supplierForest_actual_001877
  · exact g32p_supplierForest_actual_001880
  · exact g32p_supplierForest_actual_001911
  · exact g32p_supplierForest_actual_001990
  · exact g32p_supplierForest_actual_002030
  · exact g32p_supplierForest_actual_002055
  · exact g32p_supplierForest_actual_002105
  · exact g32p_supplierForest_actual_002129
  · exact g32p_supplierForest_actual_002152
  · exact g32p_supplierForest_actual_002294
  · exact g32p_supplierForest_actual_002329
  · exact g32p_supplierForest_actual_002373
  · exact g32p_supplierForest_actual_002393
  · exact g32p_supplierForest_actual_002396
  · exact g32p_supplierForest_actual_002482
  · exact g32p_supplierForest_actual_002515
  · exact g32p_supplierForest_actual_002525
  · exact g32p_supplierForest_actual_002578
  · exact g32p_supplierForest_actual_002636
  · exact g32p_supplierForest_actual_002684
  · exact g32p_supplierForest_actual_002714
  · exact g32p_supplierForest_actual_002756
  · exact g32p_supplierForest_actual_002810
  · exact g32p_supplierForest_actual_002822
  · exact g32p_supplierForest_actual_002855
  · exact g32p_supplierForest_actual_002869
  · exact g32p_supplierForest_actual_002895
  · exact g32p_supplierForest_actual_002990
  · exact g32p_supplierForest_actual_003009
  · exact g32p_supplierForest_actual_003013
  · exact g32p_supplierForest_actual_003016
  · exact g32p_supplierForest_actual_003031
  · exact g32p_supplierForest_actual_003065
  · exact g32p_supplierForest_actual_003069
  · exact g32p_supplierForest_actual_003085
  · exact g32p_supplierForest_actual_003100
  · exact g32p_supplierForest_actual_003111
  · exact g32p_supplierForest_actual_003116
  · exact g32p_supplierForest_actual_003120
  · exact g32p_supplierForest_actual_003144
  · exact g32p_supplierForest_actual_003148
  · exact g32p_supplierForest_actual_003174
  · exact g32p_supplierForest_actual_003182
  · exact g32p_supplierForest_actual_003184
  · exact g32p_supplierForest_actual_003208
  · exact g32p_supplierForest_actual_003239
  · exact g32p_supplierForest_actual_003264
  · exact g32p_supplierForest_actual_003278
  · exact g32p_supplierForest_actual_003300
  · exact g32p_supplierForest_actual_003319
  · exact g32p_supplierForest_actual_003372
  · exact g32p_supplierForest_actual_003393
  · exact g32p_supplierForest_actual_003406
  · exact g32p_supplierForest_actual_003409
  · exact g32p_supplierForest_actual_003413
  · exact g32p_supplierForest_actual_003423
  · exact g32p_supplierForest_actual_003456
  · exact g32p_supplierForest_actual_003467
  · exact g32p_supplierForest_actual_003475
  · exact g32p_supplierForest_actual_003566
  · exact g32p_supplierForest_actual_003570
  · exact g32p_supplierForest_actual_003599
  · exact g32p_supplierForest_actual_003600
  · exact g32p_supplierForest_actual_003655
  · exact g32p_supplierForest_actual_003657
  · exact g32p_supplierForest_actual_003668
  · exact g32p_supplierForest_actual_003679
  · exact g32p_supplierForest_actual_003717
  · exact g32p_supplierForest_actual_003768
  · exact g32p_supplierForest_actual_003821
  · exact g32p_supplierForest_actual_003827
  · exact g32p_supplierForest_actual_003836
  · exact g32p_supplierForest_actual_003840
  · exact g32p_supplierForest_actual_003851
  · exact g32p_supplierForest_actual_003854
  · exact g32p_supplierForest_actual_003861
  · exact g32p_supplierForest_actual_003868
  · exact g32p_supplierForest_actual_003882
  · exact g32p_supplierForest_actual_003883
  · exact g32p_supplierForest_actual_003924
  · exact g32p_supplierForest_actual_003984
  · exact g32p_supplierForest_actual_004033
  · exact g32p_supplierForest_actual_004066
  · exact g32p_supplierForest_actual_004070
  · exact g32p_supplierForest_actual_004085
  · exact g32p_supplierForest_actual_004147
  · exact g32p_supplierForest_actual_004235
  · exact g32p_supplierForest_actual_004300
  · exact g32p_supplierForest_actual_004335
  · exact g32p_supplierForest_actual_004366
  · exact g32p_supplierForest_actual_004377
  · exact g32p_supplierForest_actual_004382
  · exact g32p_supplierForest_actual_004404
  · exact g32p_supplierForest_actual_004461
  · exact g32p_supplierForest_actual_004508
  · exact g32p_supplierForest_actual_004521
  · exact g32p_supplierForest_actual_004550
  · exact g32p_supplierForest_actual_004582
  · exact g32p_supplierForest_actual_004595
  · exact g32p_supplierForest_actual_004614
  · exact g32p_supplierForest_actual_004664
  · exact g32p_supplierForest_actual_004715
  · exact g32p_supplierForest_actual_004751
  · exact g32p_supplierForest_actual_004762
  · exact g32p_supplierForest_actual_004780
  · exact g32p_supplierForest_actual_004807
  · exact g32p_supplierForest_actual_004838
  · exact g32p_supplierForest_actual_004866
  · exact g32p_supplierForest_actual_004869
  · exact g32p_supplierForest_actual_004879
  · exact g32p_supplierForest_actual_004889
  · exact g32p_supplierForest_actual_004945
  · exact g32p_supplierForest_actual_004967
  · exact g32p_supplierForest_actual_004970
  · exact g32p_supplierForest_actual_004980
  · exact g32p_supplierForest_actual_004990
  · exact g32p_supplierForest_actual_004991
  · exact g32p_supplierForest_actual_005067
  · exact g32p_supplierForest_actual_005175
  · exact g32p_supplierForest_actual_005254
  · exact g32p_supplierForest_actual_005255
  · exact g32p_supplierForest_actual_005261
  · exact g32p_supplierForest_actual_005265
  · exact g32p_supplierForest_actual_005311
  · exact g32p_supplierForest_actual_005383
  · exact g32p_supplierForest_actual_005387
  · exact g32p_supplierForest_actual_005436
  · exact g32p_supplierForest_actual_005487
  · exact g32p_supplierForest_actual_005498
  · exact g32p_supplierForest_actual_005524
  · exact g32p_supplierForest_actual_005528
  · exact g32p_supplierForest_actual_005559
  · exact g32p_supplierForest_actual_005601
  · exact g32p_supplierForest_actual_005673
  · exact g32p_supplierForest_actual_005729
  · exact g32p_supplierForest_actual_005793
  · exact g32p_supplierForest_actual_005796
  · exact g32p_supplierForest_actual_005799
  · exact g32p_supplierForest_actual_005835
  · exact g32p_supplierForest_actual_005864
  · exact g32p_supplierForest_actual_005911
  · exact g32p_supplierForest_actual_005912
  · exact g32p_supplierForest_actual_005923
  · exact g32p_supplierForest_actual_005931
  · exact g32p_supplierForest_actual_005963
  · exact g32p_supplierForest_actual_005984
  · exact g32p_supplierForest_actual_005993
  · exact g32p_supplierForest_actual_006002
  · exact g32p_supplierForest_actual_006059
  · exact g32p_supplierForest_actual_006071
  · exact g32p_supplierForest_actual_006077
  · exact g32p_supplierForest_actual_006098
  · exact g32p_supplierForest_actual_006102
  · exact g32p_supplierForest_actual_006137
  · exact g32p_supplierForest_actual_006146
  · exact g32p_supplierForest_actual_006167
  · exact g32p_supplierForest_actual_006200
  · exact g32p_supplierForest_actual_006235
  · exact g32p_supplierForest_actual_006270
  · exact g32p_supplierForest_actual_006271
  · exact g32p_supplierForest_actual_006289
  · exact g32p_supplierForest_actual_006356
  · exact g32p_supplierForest_actual_006383
  · exact g32p_supplierForest_actual_006388
  · exact g32p_supplierForest_actual_006407
  · exact g32p_supplierForest_actual_006413
  · exact g32p_supplierForest_actual_006418
  · exact g32p_supplierForest_actual_006446
  · exact g32p_supplierForest_actual_006454
  · exact g32p_supplierForest_actual_006517
  · exact g32p_supplierForest_actual_006524
  · exact g32p_supplierForest_actual_006569
  · exact g32p_supplierForest_actual_006572
  · exact g32p_supplierForest_actual_006587
  · exact g32p_supplierForest_actual_006599
  · exact g32p_supplierForest_actual_006675
  · exact g32p_supplierForest_actual_006750
  · exact g32p_supplierForest_actual_006785
  · exact g32p_supplierForest_actual_006807
  · exact g32p_supplierForest_actual_006855
  · exact g32p_supplierForest_actual_006865
  · exact g32p_supplierForest_actual_006874
  · exact g32p_supplierForest_actual_006911
  · exact g32p_supplierForest_actual_006986
  · exact g32p_supplierForest_actual_007004
  · exact g32p_supplierForest_actual_007033
  · exact g32p_supplierForest_actual_007037
  · exact g32p_supplierForest_actual_007043
  · exact g32p_supplierForest_actual_007067
  · exact g32p_supplierForest_actual_007090
  · exact g32p_supplierForest_actual_007126
  · exact g32p_supplierForest_actual_007149
  · exact g32p_supplierForest_actual_007155
  · exact g32p_supplierForest_actual_007170
  · exact g32p_supplierForest_actual_007183
  · exact g32p_supplierForest_actual_007237
  · exact g32p_supplierForest_actual_007239
  · exact g32p_supplierForest_actual_007250
  · exact g32p_supplierForest_actual_007271
  · exact g32p_supplierForest_actual_007283
  · exact g32p_supplierForest_actual_007299
  · exact g32p_supplierForest_actual_007306
  · exact g32p_supplierForest_actual_007399
  · exact g32p_supplierForest_actual_007426
  · exact g32p_supplierForest_actual_007472
  · exact g32p_supplierForest_actual_007490
  · exact g32p_supplierForest_actual_007704
  · exact g32p_supplierForest_actual_007755
  · exact g32p_supplierForest_actual_007760
  · exact g32p_supplierForest_actual_007800
  · exact g32p_supplierForest_actual_007810
  · exact g32p_supplierForest_actual_007861
  · exact g32p_supplierForest_actual_007897
  · exact g32p_supplierForest_actual_007930
  · exact g32p_supplierForest_actual_007936
  · exact g32p_supplierForest_actual_007960
  · exact g32p_supplierForest_actual_008007
  · exact g32p_supplierForest_actual_008026
  · exact g32p_supplierForest_actual_008030
  · exact g32p_supplierForest_actual_008044
  · exact g32p_supplierForest_actual_008047
  · exact g32p_supplierForest_actual_008066
  · exact g32p_supplierForest_actual_008078
  · exact g32p_supplierForest_actual_008080
  · exact g32p_supplierForest_actual_008083
  · exact g32p_supplierForest_actual_008086
  · exact g32p_supplierForest_actual_008107
  · exact g32p_supplierForest_actual_008109
  · exact g32p_supplierForest_actual_008114
  · exact g32p_supplierForest_actual_008131
  · exact g32p_supplierForest_actual_008146
  · exact g32p_supplierForest_actual_008156
  · exact g32p_supplierForest_actual_008180
  · exact g32p_supplierForest_actual_008185
  · exact g32p_supplierForest_actual_008248
  · exact g32p_supplierForest_actual_008338
  · exact g32p_supplierForest_actual_008340
  · exact g32p_supplierForest_actual_008363
  · exact g32p_supplierForest_actual_008366
  · exact g32p_supplierForest_actual_008401
  · exact g32p_supplierForest_actual_008417
  · exact g32p_supplierForest_actual_008441
  · exact g32p_supplierForest_actual_008461
  · exact g32p_supplierForest_actual_008489
  · exact g32p_supplierForest_actual_008493
  · exact g32p_supplierForest_actual_008505

def g32p_supplierForest_nodes_033 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_008518 else g32p_supplierForest_node_008550) else (if i.val < 3 then g32p_supplierForest_node_008555 else g32p_supplierForest_node_008559)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_008594 else g32p_supplierForest_node_008608) else (if i.val < 7 then g32p_supplierForest_node_008658 else g32p_supplierForest_node_008667))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_008670 else g32p_supplierForest_node_008673) else (if i.val < 11 then g32p_supplierForest_node_008699 else g32p_supplierForest_node_008715)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_008716 else g32p_supplierForest_node_008767) else (if i.val < 15 then g32p_supplierForest_node_008804 else g32p_supplierForest_node_008856)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_008857 else g32p_supplierForest_node_008885) else (if i.val < 19 then g32p_supplierForest_node_008923 else g32p_supplierForest_node_008924)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_008941 else g32p_supplierForest_node_008944) else (if i.val < 23 then g32p_supplierForest_node_008962 else g32p_supplierForest_node_008976))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_009050 else g32p_supplierForest_node_009084) else (if i.val < 27 then g32p_supplierForest_node_009088 else g32p_supplierForest_node_009124)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_009134 else g32p_supplierForest_node_009191) else (if i.val < 31 then g32p_supplierForest_node_009236 else g32p_supplierForest_node_009253))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_009271 else g32p_supplierForest_node_009327) else (if i.val < 35 then g32p_supplierForest_node_009380 else g32p_supplierForest_node_009381)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_009425 else g32p_supplierForest_node_009450) else (if i.val < 39 then g32p_supplierForest_node_009500 else g32p_supplierForest_node_009543))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_009547 else g32p_supplierForest_node_009558) else (if i.val < 43 then g32p_supplierForest_node_009564 else g32p_supplierForest_node_009575)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_009625 else g32p_supplierForest_node_009654) else (if i.val < 47 then g32p_supplierForest_node_009659 else g32p_supplierForest_node_009664)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_009683 else g32p_supplierForest_node_009710) else (if i.val < 51 then g32p_supplierForest_node_009747 else g32p_supplierForest_node_009799)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_009808 else g32p_supplierForest_node_009829) else (if i.val < 55 then g32p_supplierForest_node_009864 else g32p_supplierForest_node_009883))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_009893 else g32p_supplierForest_node_009905) else (if i.val < 59 then g32p_supplierForest_node_009906 else g32p_supplierForest_node_009988)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_010004 else g32p_supplierForest_node_010021) else (if i.val < 63 then g32p_supplierForest_node_010044 else g32p_supplierForest_node_010045)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_010057 else g32p_supplierForest_node_010080) else (if i.val < 67 then g32p_supplierForest_node_010104 else g32p_supplierForest_node_010157)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_010163 else g32p_supplierForest_node_010216) else (if i.val < 71 then g32p_supplierForest_node_010226 else g32p_supplierForest_node_010271))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_010311 else g32p_supplierForest_node_010329) else (if i.val < 75 then g32p_supplierForest_node_010432 else g32p_supplierForest_node_010453)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_010529 else g32p_supplierForest_node_010658) else (if i.val < 79 then g32p_supplierForest_node_010665 else g32p_supplierForest_node_010691)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_010711 else g32p_supplierForest_node_010739) else (if i.val < 83 then g32p_supplierForest_node_010745 else g32p_supplierForest_node_010750)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_010768 else g32p_supplierForest_node_010774) else (if i.val < 87 then g32p_supplierForest_node_010787 else g32p_supplierForest_node_010843))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_010963 else g32p_supplierForest_node_010981) else (if i.val < 91 then g32p_supplierForest_node_011030 else g32p_supplierForest_node_011045)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_011046 else g32p_supplierForest_node_011083) else (if i.val < 95 then g32p_supplierForest_node_011112 else g32p_supplierForest_node_011129))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_011133 else g32p_supplierForest_node_011138) else (if i.val < 99 then g32p_supplierForest_node_011144 else g32p_supplierForest_node_011164)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_011216 else g32p_supplierForest_node_011225) else (if i.val < 103 then g32p_supplierForest_node_011243 else g32p_supplierForest_node_011265))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_011327 else g32p_supplierForest_node_011367) else (if i.val < 107 then g32p_supplierForest_node_011378 else g32p_supplierForest_node_011388)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_011392 else g32p_supplierForest_node_011429) else (if i.val < 111 then g32p_supplierForest_node_011443 else g32p_supplierForest_node_011484)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_011498 else g32p_supplierForest_node_011505) else (if i.val < 115 then g32p_supplierForest_node_011524 else g32p_supplierForest_node_011540)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_011542 else g32p_supplierForest_node_011571) else (if i.val < 119 then g32p_supplierForest_node_011576 else g32p_supplierForest_node_011583))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_011613 else g32p_supplierForest_node_011658) else (if i.val < 123 then g32p_supplierForest_node_011668 else g32p_supplierForest_node_011675)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_011682 else g32p_supplierForest_node_011698) else (if i.val < 127 then g32p_supplierForest_node_011707 else g32p_supplierForest_node_011718))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_011735 else g32p_supplierForest_node_011748) else (if i.val < 131 then g32p_supplierForest_node_011826 else g32p_supplierForest_node_011828)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_011837 else g32p_supplierForest_node_011839) else (if i.val < 135 then g32p_supplierForest_node_011855 else g32p_supplierForest_node_011877))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_011901 else g32p_supplierForest_node_011927) else (if i.val < 139 then g32p_supplierForest_node_011993 else g32p_supplierForest_node_012115)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_012177 else g32p_supplierForest_node_012196) else (if i.val < 143 then g32p_supplierForest_node_012212 else g32p_supplierForest_node_012236)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_012273 else g32p_supplierForest_node_012282) else (if i.val < 147 then g32p_supplierForest_node_012316 else g32p_supplierForest_node_012318)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_012332 else g32p_supplierForest_node_012349) else (if i.val < 151 then g32p_supplierForest_node_012375 else g32p_supplierForest_node_012385))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_012412 else g32p_supplierForest_node_012424) else (if i.val < 155 then g32p_supplierForest_node_012484 else g32p_supplierForest_node_012491)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_012492 else g32p_supplierForest_node_012524) else (if i.val < 159 then g32p_supplierForest_node_012544 else g32p_supplierForest_node_012558))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_012568 else g32p_supplierForest_node_012586) else (if i.val < 163 then g32p_supplierForest_node_012602 else g32p_supplierForest_node_012608)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_012618 else g32p_supplierForest_node_012623) else (if i.val < 167 then g32p_supplierForest_node_012626 else g32p_supplierForest_node_012633))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_012654 else g32p_supplierForest_node_012698) else (if i.val < 171 then g32p_supplierForest_node_012740 else g32p_supplierForest_node_012779)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_012788 else g32p_supplierForest_node_012800) else (if i.val < 175 then g32p_supplierForest_node_012801 else g32p_supplierForest_node_012808)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_012821 else g32p_supplierForest_node_012823) else (if i.val < 179 then g32p_supplierForest_node_012829 else g32p_supplierForest_node_012850)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_012866 else g32p_supplierForest_node_012880) else (if i.val < 183 then g32p_supplierForest_node_012941 else g32p_supplierForest_node_012950))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_012964 else g32p_supplierForest_node_012965) else (if i.val < 187 then g32p_supplierForest_node_012976 else g32p_supplierForest_node_012979)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_012987 else g32p_supplierForest_node_013022) else (if i.val < 191 then g32p_supplierForest_node_013052 else g32p_supplierForest_node_013053)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_013135 else g32p_supplierForest_node_013146) else (if i.val < 195 then g32p_supplierForest_node_013158 else g32p_supplierForest_node_013180)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_013198 else g32p_supplierForest_node_013217) else (if i.val < 199 then g32p_supplierForest_node_013236 else g32p_supplierForest_node_013242))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_013272 else g32p_supplierForest_node_013290) else (if i.val < 203 then g32p_supplierForest_node_013307 else g32p_supplierForest_node_013310)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_013317 else g32p_supplierForest_node_013325) else (if i.val < 207 then g32p_supplierForest_node_013358 else g32p_supplierForest_node_013387)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_013412 else g32p_supplierForest_node_013427) else (if i.val < 211 then g32p_supplierForest_node_013449 else g32p_supplierForest_node_013514)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_013535 else g32p_supplierForest_node_013536) else (if i.val < 215 then g32p_supplierForest_node_013589 else g32p_supplierForest_node_013619))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_013633 else g32p_supplierForest_node_013634) else (if i.val < 219 then g32p_supplierForest_node_013663 else g32p_supplierForest_node_013720)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_013757 else g32p_supplierForest_node_013791) else (if i.val < 223 then g32p_supplierForest_node_013810 else g32p_supplierForest_node_013856))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_013860 else g32p_supplierForest_node_013885) else (if i.val < 227 then g32p_supplierForest_node_013892 else g32p_supplierForest_node_013925)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_013970 else g32p_supplierForest_node_013978) else (if i.val < 231 then g32p_supplierForest_node_014014 else g32p_supplierForest_node_014056))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_014063 else g32p_supplierForest_node_014087) else (if i.val < 235 then g32p_supplierForest_node_014116 else g32p_supplierForest_node_014117)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_014178 else g32p_supplierForest_node_014184) else (if i.val < 239 then g32p_supplierForest_node_014189 else g32p_supplierForest_node_014198)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_014239 else g32p_supplierForest_node_014245) else (if i.val < 243 then g32p_supplierForest_node_014263 else g32p_supplierForest_node_014276)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_014283 else g32p_supplierForest_node_014297) else (if i.val < 247 then g32p_supplierForest_node_014327 else g32p_supplierForest_node_014336))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_014351 else g32p_supplierForest_node_014367) else (if i.val < 251 then g32p_supplierForest_node_014389 else g32p_supplierForest_node_014402)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_014407 else g32p_supplierForest_node_014414) else (if i.val < 255 then g32p_supplierForest_node_014453 else g32p_supplierForest_node_014457))))))))

def g32p_supplierForest_classes_033 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 21 else 21) else (if i.val < 3 then 39 else 24)) else (if i.val < 6 then (if i.val < 5 then 39 else 20) else (if i.val < 7 then 20 else 24))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 22) else (if i.val < 11 then 21 else 20)) else (if i.val < 14 then (if i.val < 13 then 38 else 5) else (if i.val < 15 then 5 else 24)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 20 else 39) else (if i.val < 19 then 38 else 39)) else (if i.val < 22 then (if i.val < 21 then 39 else 5) else (if i.val < 23 then 40 else 6))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 7 else 38) else (if i.val < 27 then 7 else 40)) else (if i.val < 30 then (if i.val < 29 then 39 else 24) else (if i.val < 31 then 22 else 5))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 5 else 5) else (if i.val < 35 then 22 else 19)) else (if i.val < 38 then (if i.val < 37 then 6 else 38) else (if i.val < 39 then 22 else 24))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 21 else 24) else (if i.val < 43 then 38 else 18)) else (if i.val < 46 then (if i.val < 45 then 21 else 22) else (if i.val < 47 then 21 else 5)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 22 else 5) else (if i.val < 51 then 22 else 6)) else (if i.val < 54 then (if i.val < 53 then 18 else 6) else (if i.val < 55 then 19 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 21 else 21) else (if i.val < 59 then 21 else 24)) else (if i.val < 62 then (if i.val < 61 then 20 else 38) else (if i.val < 63 then 21 else 22)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 20 else 22) else (if i.val < 67 then 42 else 24)) else (if i.val < 70 then (if i.val < 69 then 21 else 39) else (if i.val < 71 then 40 else 5))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 21 else 7) else (if i.val < 75 then 40 else 39)) else (if i.val < 78 then (if i.val < 77 then 21 else 7) else (if i.val < 79 then 40 else 40)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 6 else 23) else (if i.val < 83 then 5 else 5)) else (if i.val < 86 then (if i.val < 85 then 38 else 22) else (if i.val < 87 then 5 else 6))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 39 else 40) else (if i.val < 91 then 39 else 38)) else (if i.val < 94 then (if i.val < 93 then 39 else 5) else (if i.val < 95 then 21 else 22))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 20 else 24) else (if i.val < 99 then 22 else 39)) else (if i.val < 102 then (if i.val < 101 then 21 else 22) else (if i.val < 103 then 20 else 39))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 24 else 7) else (if i.val < 107 then 6 else 21)) else (if i.val < 110 then (if i.val < 109 then 22 else 38) else (if i.val < 111 then 7 else 24)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 19 else 40) else (if i.val < 115 then 40 else 24)) else (if i.val < 118 then (if i.val < 117 then 40 else 38) else (if i.val < 119 then 5 else 23))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 21 else 24) else (if i.val < 123 then 5 else 24)) else (if i.val < 126 then (if i.val < 125 then 7 else 24) else (if i.val < 127 then 38 else 6))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 20 else 21) else (if i.val < 131 then 39 else 22)) else (if i.val < 134 then (if i.val < 133 then 22 else 40) else (if i.val < 135 then 19 else 40))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 6 else 7) else (if i.val < 139 then 20 else 7)) else (if i.val < 142 then (if i.val < 141 then 5 else 7) else (if i.val < 143 then 38 else 7)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 23 else 38) else (if i.val < 147 then 23 else 22)) else (if i.val < 150 then (if i.val < 149 then 8 else 10) else (if i.val < 151 then 10 else 27))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 47 else 10) else (if i.val < 155 then 47 else 10)) else (if i.val < 158 then (if i.val < 157 then 26 else 26) else (if i.val < 159 then 48 else 10))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 10 else 47) else (if i.val < 163 then 49 else 49)) else (if i.val < 166 then (if i.val < 165 then 10 else 50) else (if i.val < 167 then 9 else 27))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 26 else 10) else (if i.val < 171 then 10 else 9)) else (if i.val < 174 then (if i.val < 173 then 8 else 27) else (if i.val < 175 then 26 else 1)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 27 else 12) else (if i.val < 179 then 26 else 11)) else (if i.val < 182 then (if i.val < 181 then 12 else 13) else (if i.val < 183 then 50 else 49))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 47 else 13) else (if i.val < 187 then 12 else 9)) else (if i.val < 190 then (if i.val < 189 then 27 else 10) else (if i.val < 191 then 26 else 13)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 12 else 1) else (if i.val < 195 then 48 else 49)) else (if i.val < 198 then (if i.val < 197 then 27 else 48) else (if i.val < 199 then 9 else 12))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 12 else 26) else (if i.val < 203 then 10 else 49)) else (if i.val < 206 then (if i.val < 205 then 49 else 13) else (if i.val < 207 then 10 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 49 else 13) else (if i.val < 211 then 8 else 56)) else (if i.val < 214 then (if i.val < 213 then 46 else 49) else (if i.val < 215 then 9 else 12))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 25 else 46) else (if i.val < 219 then 13 else 10)) else (if i.val < 222 then (if i.val < 221 then 13 else 28) else (if i.val < 223 then 9 else 13))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 27 else 25) else (if i.val < 227 then 26 else 10)) else (if i.val < 230 then (if i.val < 229 then 46 else 25) else (if i.val < 231 then 50 else 12))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 10 else 27) else (if i.val < 235 then 13 else 25)) else (if i.val < 238 then (if i.val < 237 then 10 else 9) else (if i.val < 239 then 8 else 48)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 9 else 10) else (if i.val < 243 then 9 else 13)) else (if i.val < 246 then (if i.val < 245 then 13 else 47) else (if i.val < 247 then 49 else 50))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 48) else (if i.val < 251 then 12 else 47)) else (if i.val < 254 then (if i.val < 253 then 10 else 27) else (if i.val < 255 then 10 else 10))))))))

theorem g32p_supplierForest_actual_033 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_033 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_033 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_008518
  · exact g32p_supplierForest_actual_008550
  · exact g32p_supplierForest_actual_008555
  · exact g32p_supplierForest_actual_008559
  · exact g32p_supplierForest_actual_008594
  · exact g32p_supplierForest_actual_008608
  · exact g32p_supplierForest_actual_008658
  · exact g32p_supplierForest_actual_008667
  · exact g32p_supplierForest_actual_008670
  · exact g32p_supplierForest_actual_008673
  · exact g32p_supplierForest_actual_008699
  · exact g32p_supplierForest_actual_008715
  · exact g32p_supplierForest_actual_008716
  · exact g32p_supplierForest_actual_008767
  · exact g32p_supplierForest_actual_008804
  · exact g32p_supplierForest_actual_008856
  · exact g32p_supplierForest_actual_008857
  · exact g32p_supplierForest_actual_008885
  · exact g32p_supplierForest_actual_008923
  · exact g32p_supplierForest_actual_008924
  · exact g32p_supplierForest_actual_008941
  · exact g32p_supplierForest_actual_008944
  · exact g32p_supplierForest_actual_008962
  · exact g32p_supplierForest_actual_008976
  · exact g32p_supplierForest_actual_009050
  · exact g32p_supplierForest_actual_009084
  · exact g32p_supplierForest_actual_009088
  · exact g32p_supplierForest_actual_009124
  · exact g32p_supplierForest_actual_009134
  · exact g32p_supplierForest_actual_009191
  · exact g32p_supplierForest_actual_009236
  · exact g32p_supplierForest_actual_009253
  · exact g32p_supplierForest_actual_009271
  · exact g32p_supplierForest_actual_009327
  · exact g32p_supplierForest_actual_009380
  · exact g32p_supplierForest_actual_009381
  · exact g32p_supplierForest_actual_009425
  · exact g32p_supplierForest_actual_009450
  · exact g32p_supplierForest_actual_009500
  · exact g32p_supplierForest_actual_009543
  · exact g32p_supplierForest_actual_009547
  · exact g32p_supplierForest_actual_009558
  · exact g32p_supplierForest_actual_009564
  · exact g32p_supplierForest_actual_009575
  · exact g32p_supplierForest_actual_009625
  · exact g32p_supplierForest_actual_009654
  · exact g32p_supplierForest_actual_009659
  · exact g32p_supplierForest_actual_009664
  · exact g32p_supplierForest_actual_009683
  · exact g32p_supplierForest_actual_009710
  · exact g32p_supplierForest_actual_009747
  · exact g32p_supplierForest_actual_009799
  · exact g32p_supplierForest_actual_009808
  · exact g32p_supplierForest_actual_009829
  · exact g32p_supplierForest_actual_009864
  · exact g32p_supplierForest_actual_009883
  · exact g32p_supplierForest_actual_009893
  · exact g32p_supplierForest_actual_009905
  · exact g32p_supplierForest_actual_009906
  · exact g32p_supplierForest_actual_009988
  · exact g32p_supplierForest_actual_010004
  · exact g32p_supplierForest_actual_010021
  · exact g32p_supplierForest_actual_010044
  · exact g32p_supplierForest_actual_010045
  · exact g32p_supplierForest_actual_010057
  · exact g32p_supplierForest_actual_010080
  · exact g32p_supplierForest_actual_010104
  · exact g32p_supplierForest_actual_010157
  · exact g32p_supplierForest_actual_010163
  · exact g32p_supplierForest_actual_010216
  · exact g32p_supplierForest_actual_010226
  · exact g32p_supplierForest_actual_010271
  · exact g32p_supplierForest_actual_010311
  · exact g32p_supplierForest_actual_010329
  · exact g32p_supplierForest_actual_010432
  · exact g32p_supplierForest_actual_010453
  · exact g32p_supplierForest_actual_010529
  · exact g32p_supplierForest_actual_010658
  · exact g32p_supplierForest_actual_010665
  · exact g32p_supplierForest_actual_010691
  · exact g32p_supplierForest_actual_010711
  · exact g32p_supplierForest_actual_010739
  · exact g32p_supplierForest_actual_010745
  · exact g32p_supplierForest_actual_010750
  · exact g32p_supplierForest_actual_010768
  · exact g32p_supplierForest_actual_010774
  · exact g32p_supplierForest_actual_010787
  · exact g32p_supplierForest_actual_010843
  · exact g32p_supplierForest_actual_010963
  · exact g32p_supplierForest_actual_010981
  · exact g32p_supplierForest_actual_011030
  · exact g32p_supplierForest_actual_011045
  · exact g32p_supplierForest_actual_011046
  · exact g32p_supplierForest_actual_011083
  · exact g32p_supplierForest_actual_011112
  · exact g32p_supplierForest_actual_011129
  · exact g32p_supplierForest_actual_011133
  · exact g32p_supplierForest_actual_011138
  · exact g32p_supplierForest_actual_011144
  · exact g32p_supplierForest_actual_011164
  · exact g32p_supplierForest_actual_011216
  · exact g32p_supplierForest_actual_011225
  · exact g32p_supplierForest_actual_011243
  · exact g32p_supplierForest_actual_011265
  · exact g32p_supplierForest_actual_011327
  · exact g32p_supplierForest_actual_011367
  · exact g32p_supplierForest_actual_011378
  · exact g32p_supplierForest_actual_011388
  · exact g32p_supplierForest_actual_011392
  · exact g32p_supplierForest_actual_011429
  · exact g32p_supplierForest_actual_011443
  · exact g32p_supplierForest_actual_011484
  · exact g32p_supplierForest_actual_011498
  · exact g32p_supplierForest_actual_011505
  · exact g32p_supplierForest_actual_011524
  · exact g32p_supplierForest_actual_011540
  · exact g32p_supplierForest_actual_011542
  · exact g32p_supplierForest_actual_011571
  · exact g32p_supplierForest_actual_011576
  · exact g32p_supplierForest_actual_011583
  · exact g32p_supplierForest_actual_011613
  · exact g32p_supplierForest_actual_011658
  · exact g32p_supplierForest_actual_011668
  · exact g32p_supplierForest_actual_011675
  · exact g32p_supplierForest_actual_011682
  · exact g32p_supplierForest_actual_011698
  · exact g32p_supplierForest_actual_011707
  · exact g32p_supplierForest_actual_011718
  · exact g32p_supplierForest_actual_011735
  · exact g32p_supplierForest_actual_011748
  · exact g32p_supplierForest_actual_011826
  · exact g32p_supplierForest_actual_011828
  · exact g32p_supplierForest_actual_011837
  · exact g32p_supplierForest_actual_011839
  · exact g32p_supplierForest_actual_011855
  · exact g32p_supplierForest_actual_011877
  · exact g32p_supplierForest_actual_011901
  · exact g32p_supplierForest_actual_011927
  · exact g32p_supplierForest_actual_011993
  · exact g32p_supplierForest_actual_012115
  · exact g32p_supplierForest_actual_012177
  · exact g32p_supplierForest_actual_012196
  · exact g32p_supplierForest_actual_012212
  · exact g32p_supplierForest_actual_012236
  · exact g32p_supplierForest_actual_012273
  · exact g32p_supplierForest_actual_012282
  · exact g32p_supplierForest_actual_012316
  · exact g32p_supplierForest_actual_012318
  · exact g32p_supplierForest_actual_012332
  · exact g32p_supplierForest_actual_012349
  · exact g32p_supplierForest_actual_012375
  · exact g32p_supplierForest_actual_012385
  · exact g32p_supplierForest_actual_012412
  · exact g32p_supplierForest_actual_012424
  · exact g32p_supplierForest_actual_012484
  · exact g32p_supplierForest_actual_012491
  · exact g32p_supplierForest_actual_012492
  · exact g32p_supplierForest_actual_012524
  · exact g32p_supplierForest_actual_012544
  · exact g32p_supplierForest_actual_012558
  · exact g32p_supplierForest_actual_012568
  · exact g32p_supplierForest_actual_012586
  · exact g32p_supplierForest_actual_012602
  · exact g32p_supplierForest_actual_012608
  · exact g32p_supplierForest_actual_012618
  · exact g32p_supplierForest_actual_012623
  · exact g32p_supplierForest_actual_012626
  · exact g32p_supplierForest_actual_012633
  · exact g32p_supplierForest_actual_012654
  · exact g32p_supplierForest_actual_012698
  · exact g32p_supplierForest_actual_012740
  · exact g32p_supplierForest_actual_012779
  · exact g32p_supplierForest_actual_012788
  · exact g32p_supplierForest_actual_012800
  · exact g32p_supplierForest_actual_012801
  · exact g32p_supplierForest_actual_012808
  · exact g32p_supplierForest_actual_012821
  · exact g32p_supplierForest_actual_012823
  · exact g32p_supplierForest_actual_012829
  · exact g32p_supplierForest_actual_012850
  · exact g32p_supplierForest_actual_012866
  · exact g32p_supplierForest_actual_012880
  · exact g32p_supplierForest_actual_012941
  · exact g32p_supplierForest_actual_012950
  · exact g32p_supplierForest_actual_012964
  · exact g32p_supplierForest_actual_012965
  · exact g32p_supplierForest_actual_012976
  · exact g32p_supplierForest_actual_012979
  · exact g32p_supplierForest_actual_012987
  · exact g32p_supplierForest_actual_013022
  · exact g32p_supplierForest_actual_013052
  · exact g32p_supplierForest_actual_013053
  · exact g32p_supplierForest_actual_013135
  · exact g32p_supplierForest_actual_013146
  · exact g32p_supplierForest_actual_013158
  · exact g32p_supplierForest_actual_013180
  · exact g32p_supplierForest_actual_013198
  · exact g32p_supplierForest_actual_013217
  · exact g32p_supplierForest_actual_013236
  · exact g32p_supplierForest_actual_013242
  · exact g32p_supplierForest_actual_013272
  · exact g32p_supplierForest_actual_013290
  · exact g32p_supplierForest_actual_013307
  · exact g32p_supplierForest_actual_013310
  · exact g32p_supplierForest_actual_013317
  · exact g32p_supplierForest_actual_013325
  · exact g32p_supplierForest_actual_013358
  · exact g32p_supplierForest_actual_013387
  · exact g32p_supplierForest_actual_013412
  · exact g32p_supplierForest_actual_013427
  · exact g32p_supplierForest_actual_013449
  · exact g32p_supplierForest_actual_013514
  · exact g32p_supplierForest_actual_013535
  · exact g32p_supplierForest_actual_013536
  · exact g32p_supplierForest_actual_013589
  · exact g32p_supplierForest_actual_013619
  · exact g32p_supplierForest_actual_013633
  · exact g32p_supplierForest_actual_013634
  · exact g32p_supplierForest_actual_013663
  · exact g32p_supplierForest_actual_013720
  · exact g32p_supplierForest_actual_013757
  · exact g32p_supplierForest_actual_013791
  · exact g32p_supplierForest_actual_013810
  · exact g32p_supplierForest_actual_013856
  · exact g32p_supplierForest_actual_013860
  · exact g32p_supplierForest_actual_013885
  · exact g32p_supplierForest_actual_013892
  · exact g32p_supplierForest_actual_013925
  · exact g32p_supplierForest_actual_013970
  · exact g32p_supplierForest_actual_013978
  · exact g32p_supplierForest_actual_014014
  · exact g32p_supplierForest_actual_014056
  · exact g32p_supplierForest_actual_014063
  · exact g32p_supplierForest_actual_014087
  · exact g32p_supplierForest_actual_014116
  · exact g32p_supplierForest_actual_014117
  · exact g32p_supplierForest_actual_014178
  · exact g32p_supplierForest_actual_014184
  · exact g32p_supplierForest_actual_014189
  · exact g32p_supplierForest_actual_014198
  · exact g32p_supplierForest_actual_014239
  · exact g32p_supplierForest_actual_014245
  · exact g32p_supplierForest_actual_014263
  · exact g32p_supplierForest_actual_014276
  · exact g32p_supplierForest_actual_014283
  · exact g32p_supplierForest_actual_014297
  · exact g32p_supplierForest_actual_014327
  · exact g32p_supplierForest_actual_014336
  · exact g32p_supplierForest_actual_014351
  · exact g32p_supplierForest_actual_014367
  · exact g32p_supplierForest_actual_014389
  · exact g32p_supplierForest_actual_014402
  · exact g32p_supplierForest_actual_014407
  · exact g32p_supplierForest_actual_014414
  · exact g32p_supplierForest_actual_014453
  · exact g32p_supplierForest_actual_014457

def g32p_supplierForest_nodes_034 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_014463 else g32p_supplierForest_node_014466) else (if i.val < 3 then g32p_supplierForest_node_014483 else g32p_supplierForest_node_014485)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_014486 else g32p_supplierForest_node_014595) else (if i.val < 7 then g32p_supplierForest_node_014603 else g32p_supplierForest_node_014604))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_014611 else g32p_supplierForest_node_014639) else (if i.val < 11 then g32p_supplierForest_node_014675 else g32p_supplierForest_node_014709)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_014767 else g32p_supplierForest_node_014778) else (if i.val < 15 then g32p_supplierForest_node_014782 else g32p_supplierForest_node_014785)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_014792 else g32p_supplierForest_node_014802) else (if i.val < 19 then g32p_supplierForest_node_014810 else g32p_supplierForest_node_014918)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_014939 else g32p_supplierForest_node_014956) else (if i.val < 23 then g32p_supplierForest_node_014958 else g32p_supplierForest_node_014964))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_014967 else g32p_supplierForest_node_014980) else (if i.val < 27 then g32p_supplierForest_node_014982 else g32p_supplierForest_node_015023)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_015056 else g32p_supplierForest_node_015062) else (if i.val < 31 then g32p_supplierForest_node_015134 else g32p_supplierForest_node_015176))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_015187 else g32p_supplierForest_node_015236) else (if i.val < 35 then g32p_supplierForest_node_015267 else g32p_supplierForest_node_015436)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_015438 else g32p_supplierForest_node_015474) else (if i.val < 39 then g32p_supplierForest_node_015477 else g32p_supplierForest_node_015487))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_015524 else g32p_supplierForest_node_015539) else (if i.val < 43 then g32p_supplierForest_node_015555 else g32p_supplierForest_node_015558)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_015571 else g32p_supplierForest_node_015584) else (if i.val < 47 then g32p_supplierForest_node_015594 else g32p_supplierForest_node_015608)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_015677 else g32p_supplierForest_node_015694) else (if i.val < 51 then g32p_supplierForest_node_015721 else g32p_supplierForest_node_015734)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_015741 else g32p_supplierForest_node_015764) else (if i.val < 55 then g32p_supplierForest_node_015797 else g32p_supplierForest_node_015834))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_015898 else g32p_supplierForest_node_015907) else (if i.val < 59 then g32p_supplierForest_node_015946 else g32p_supplierForest_node_015953)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_015964 else g32p_supplierForest_node_015978) else (if i.val < 63 then g32p_supplierForest_node_015984 else g32p_supplierForest_node_015993)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_015995 else g32p_supplierForest_node_016039) else (if i.val < 67 then g32p_supplierForest_node_016040 else g32p_supplierForest_node_016080)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_016123 else g32p_supplierForest_node_016171) else (if i.val < 71 then g32p_supplierForest_node_016181 else g32p_supplierForest_node_016216))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_016228 else g32p_supplierForest_node_016244) else (if i.val < 75 then g32p_supplierForest_node_016266 else g32p_supplierForest_node_016283)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_016289 else g32p_supplierForest_node_016291) else (if i.val < 79 then g32p_supplierForest_node_016307 else g32p_supplierForest_node_016368)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_016372 else g32p_supplierForest_node_016373) else (if i.val < 83 then g32p_supplierForest_node_016384 else g32p_supplierForest_node_016393)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_016398 else g32p_supplierForest_node_016432) else (if i.val < 87 then g32p_supplierForest_node_016434 else g32p_supplierForest_node_016437))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_016440 else g32p_supplierForest_node_016491) else (if i.val < 91 then g32p_supplierForest_node_016526 else g32p_supplierForest_node_016536)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_016572 else g32p_supplierForest_node_016600) else (if i.val < 95 then g32p_supplierForest_node_016613 else g32p_supplierForest_node_016619))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_016628 else g32p_supplierForest_node_016650) else (if i.val < 99 then g32p_supplierForest_node_016652 else g32p_supplierForest_node_016663)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_016673 else g32p_supplierForest_node_016721) else (if i.val < 103 then g32p_supplierForest_node_016740 else g32p_supplierForest_node_016814))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_016827 else g32p_supplierForest_node_016829) else (if i.val < 107 then g32p_supplierForest_node_016847 else g32p_supplierForest_node_016853)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_016893 else g32p_supplierForest_node_016934) else (if i.val < 111 then g32p_supplierForest_node_017022 else g32p_supplierForest_node_017024)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_017168 else g32p_supplierForest_node_017220) else (if i.val < 115 then g32p_supplierForest_node_017226 else g32p_supplierForest_node_017232)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_017236 else g32p_supplierForest_node_017324) else (if i.val < 119 then g32p_supplierForest_node_017335 else g32p_supplierForest_node_017336))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_017401 else g32p_supplierForest_node_017457) else (if i.val < 123 then g32p_supplierForest_node_017460 else g32p_supplierForest_node_017510)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_017523 else g32p_supplierForest_node_017582) else (if i.val < 127 then g32p_supplierForest_node_017591 else g32p_supplierForest_node_017592))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_017706 else g32p_supplierForest_node_017716) else (if i.val < 131 then g32p_supplierForest_node_017762 else g32p_supplierForest_node_017777)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_017807 else g32p_supplierForest_node_017849) else (if i.val < 135 then g32p_supplierForest_node_017851 else g32p_supplierForest_node_017888))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_017890 else g32p_supplierForest_node_017902) else (if i.val < 139 then g32p_supplierForest_node_017915 else g32p_supplierForest_node_017962)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_018006 else g32p_supplierForest_node_018034) else (if i.val < 143 then g32p_supplierForest_node_018038 else g32p_supplierForest_node_018080)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_018108 else g32p_supplierForest_node_018141) else (if i.val < 147 then g32p_supplierForest_node_018228 else g32p_supplierForest_node_018251)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_018303 else g32p_supplierForest_node_018357) else (if i.val < 151 then g32p_supplierForest_node_018358 else g32p_supplierForest_node_018362))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_018410 else g32p_supplierForest_node_018423) else (if i.val < 155 then g32p_supplierForest_node_018486 else g32p_supplierForest_node_018501)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_018502 else g32p_supplierForest_node_018518) else (if i.val < 159 then g32p_supplierForest_node_018520 else g32p_supplierForest_node_018530))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_018536 else g32p_supplierForest_node_018567) else (if i.val < 163 then g32p_supplierForest_node_018579 else g32p_supplierForest_node_018586)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_018603 else g32p_supplierForest_node_018608) else (if i.val < 167 then g32p_supplierForest_node_018619 else g32p_supplierForest_node_018623))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_018626 else g32p_supplierForest_node_018636) else (if i.val < 171 then g32p_supplierForest_node_018639 else g32p_supplierForest_node_018668)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_018709 else g32p_supplierForest_node_018765) else (if i.val < 175 then g32p_supplierForest_node_018776 else g32p_supplierForest_node_018894)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_018950 else g32p_supplierForest_node_018981) else (if i.val < 179 then g32p_supplierForest_node_018983 else g32p_supplierForest_node_018984)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_019019 else g32p_supplierForest_node_019059) else (if i.val < 183 then g32p_supplierForest_node_019070 else g32p_supplierForest_node_019077))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_019078 else g32p_supplierForest_node_019178) else (if i.val < 187 then g32p_supplierForest_node_019197 else g32p_supplierForest_node_019199)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_019208 else g32p_supplierForest_node_019214) else (if i.val < 191 then g32p_supplierForest_node_019233 else g32p_supplierForest_node_019244)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_019275 else g32p_supplierForest_node_019376) else (if i.val < 195 then g32p_supplierForest_node_019378 else g32p_supplierForest_node_019397)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_019420 else g32p_supplierForest_node_019444) else (if i.val < 199 then g32p_supplierForest_node_019522 else g32p_supplierForest_node_019535))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_019562 else g32p_supplierForest_node_019581) else (if i.val < 203 then g32p_supplierForest_node_019584 else g32p_supplierForest_node_019611)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_019636 else g32p_supplierForest_node_019732) else (if i.val < 207 then g32p_supplierForest_node_019794 else g32p_supplierForest_node_019796)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_019824 else g32p_supplierForest_node_019830) else (if i.val < 211 then g32p_supplierForest_node_019919 else g32p_supplierForest_node_019930)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_019938 else g32p_supplierForest_node_019952) else (if i.val < 215 then g32p_supplierForest_node_019995 else g32p_supplierForest_node_020012))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_020044 else g32p_supplierForest_node_020070) else (if i.val < 219 then g32p_supplierForest_node_020071 else g32p_supplierForest_node_020091)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_020126 else g32p_supplierForest_node_020173) else (if i.val < 223 then g32p_supplierForest_node_020180 else g32p_supplierForest_node_020191))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_020192 else g32p_supplierForest_node_020216) else (if i.val < 227 then g32p_supplierForest_node_020230 else g32p_supplierForest_node_020241)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_020264 else g32p_supplierForest_node_020293) else (if i.val < 231 then g32p_supplierForest_node_020310 else g32p_supplierForest_node_020335))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_020338 else g32p_supplierForest_node_020363) else (if i.val < 235 then g32p_supplierForest_node_020384 else g32p_supplierForest_node_020395)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_020397 else g32p_supplierForest_node_020402) else (if i.val < 239 then g32p_supplierForest_node_020409 else g32p_supplierForest_node_020414)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_020452 else g32p_supplierForest_node_020459) else (if i.val < 243 then g32p_supplierForest_node_020490 else g32p_supplierForest_node_020506)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_020542 else g32p_supplierForest_node_020563) else (if i.val < 247 then g32p_supplierForest_node_020569 else g32p_supplierForest_node_020573))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_020581 else g32p_supplierForest_node_020607) else (if i.val < 251 then g32p_supplierForest_node_020618 else g32p_supplierForest_node_020625)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_020660 else g32p_supplierForest_node_020663) else (if i.val < 255 then g32p_supplierForest_node_020667 else g32p_supplierForest_node_020669))))))))

def g32p_supplierForest_classes_034 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 50 else 27) else (if i.val < 3 then 47 else 10)) else (if i.val < 6 then (if i.val < 5 then 12 else 50) else (if i.val < 7 then 25 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 13 else 47) else (if i.val < 11 then 49 else 12)) else (if i.val < 14 then (if i.val < 13 then 27 else 50) else (if i.val < 15 then 47 else 12)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 49 else 49) else (if i.val < 19 then 48 else 27)) else (if i.val < 22 then (if i.val < 21 then 25 else 12) else (if i.val < 23 then 47 else 9))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 50 else 10) else (if i.val < 27 then 46 else 47)) else (if i.val < 30 then (if i.val < 29 then 27 else 13) else (if i.val < 31 then 46 else 48))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 26 else 8) else (if i.val < 35 then 51 else 49)) else (if i.val < 38 then (if i.val < 37 then 47 else 48) else (if i.val < 39 then 47 else 25))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 47 else 50) else (if i.val < 43 then 49 else 13)) else (if i.val < 46 then (if i.val < 45 then 51 else 49) else (if i.val < 47 then 49 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 47 else 9) else (if i.val < 51 then 47 else 46)) else (if i.val < 54 then (if i.val < 53 then 49 else 10) else (if i.val < 55 then 48 else 27))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 10 else 49) else (if i.val < 59 then 10 else 47)) else (if i.val < 62 then (if i.val < 61 then 50 else 10) else (if i.val < 63 then 50 else 56)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 51 else 10) else (if i.val < 67 then 10 else 51)) else (if i.val < 70 then (if i.val < 69 then 51 else 12) else (if i.val < 71 then 49 else 47))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 51 else 51) else (if i.val < 75 then 46 else 47)) else (if i.val < 78 then (if i.val < 77 then 12 else 13) else (if i.val < 79 then 49 else 49)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 49 else 49) else (if i.val < 83 then 50 else 47)) else (if i.val < 86 then (if i.val < 85 then 10 else 49) else (if i.val < 87 then 47 else 48))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 10 else 49) else (if i.val < 91 then 51 else 27)) else (if i.val < 94 then (if i.val < 93 then 47 else 10) else (if i.val < 95 then 51 else 51))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 51 else 49) else (if i.val < 99 then 48 else 10)) else (if i.val < 102 then (if i.val < 101 then 49 else 28) else (if i.val < 103 then 10 else 12))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 12 else 48) else (if i.val < 107 then 10 else 49)) else (if i.val < 110 then (if i.val < 109 then 10 else 13) else (if i.val < 111 then 25 else 13)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 10 else 25) else (if i.val < 115 then 10 else 9)) else (if i.val < 118 then (if i.val < 117 then 8 else 46) else (if i.val < 119 then 25 else 13))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 26 else 27) else (if i.val < 123 then 13 else 47)) else (if i.val < 126 then (if i.val < 125 then 13 else 27) else (if i.val < 127 then 9 else 47))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 47 else 27) else (if i.val < 131 then 27 else 25)) else (if i.val < 134 then (if i.val < 133 then 8 else 47) else (if i.val < 135 then 26 else 13))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 47 else 26) else (if i.val < 139 then 48 else 27)) else (if i.val < 142 then (if i.val < 141 then 12 else 9) else (if i.val < 143 then 11 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 27 else 12) else (if i.val < 147 then 25 else 26)) else (if i.val < 150 then (if i.val < 149 then 10 else 25) else (if i.val < 151 then 46 else 13))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 27 else 8) else (if i.val < 155 then 47 else 49)) else (if i.val < 158 then (if i.val < 157 then 49 else 26) else (if i.val < 159 then 48 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 51 else 51) else (if i.val < 163 then 13 else 49)) else (if i.val < 166 then (if i.val < 165 then 48 else 46) else (if i.val < 167 then 10 else 51))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 47 else 51) else (if i.val < 171 then 10 else 10)) else (if i.val < 174 then (if i.val < 173 then 10 else 51) else (if i.val < 175 then 49 else 47)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 48 else 47) else (if i.val < 179 then 27 else 26)) else (if i.val < 182 then (if i.val < 181 then 8 else 25) else (if i.val < 183 then 9 else 47))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 27 else 10) else (if i.val < 187 then 25 else 13)) else (if i.val < 190 then (if i.val < 189 then 47 else 9) else (if i.val < 191 then 27 else 10)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 25 else 26) else (if i.val < 195 then 12 else 26)) else (if i.val < 198 then (if i.val < 197 then 13 else 10) else (if i.val < 199 then 11 else 49))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 47 else 46) else (if i.val < 203 then 50 else 13)) else (if i.val < 206 then (if i.val < 205 then 10 else 27) else (if i.val < 207 then 27 else 46)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 26 else 13) else (if i.val < 211 then 27 else 50)) else (if i.val < 214 then (if i.val < 213 then 8 else 9) else (if i.val < 215 then 12 else 10))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 13 else 50) else (if i.val < 219 then 9 else 47)) else (if i.val < 222 then (if i.val < 221 then 48 else 49) else (if i.val < 223 then 9 else 25))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 25 else 25) else (if i.val < 227 then 47 else 50)) else (if i.val < 230 then (if i.val < 229 then 47 else 49) else (if i.val < 231 then 27 else 26))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 48 else 13) else (if i.val < 235 then 50 else 12)) else (if i.val < 238 then (if i.val < 237 then 13 else 47) else (if i.val < 239 then 48 else 12)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 48 else 27) else (if i.val < 243 then 47 else 12)) else (if i.val < 246 then (if i.val < 245 then 9 else 47) else (if i.val < 247 then 46 else 11))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 13 else 27) else (if i.val < 251 then 26 else 12)) else (if i.val < 254 then (if i.val < 253 then 46 else 49) else (if i.val < 255 then 12 else 13))))))))

theorem g32p_supplierForest_actual_034 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_034 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_034 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_014463
  · exact g32p_supplierForest_actual_014466
  · exact g32p_supplierForest_actual_014483
  · exact g32p_supplierForest_actual_014485
  · exact g32p_supplierForest_actual_014486
  · exact g32p_supplierForest_actual_014595
  · exact g32p_supplierForest_actual_014603
  · exact g32p_supplierForest_actual_014604
  · exact g32p_supplierForest_actual_014611
  · exact g32p_supplierForest_actual_014639
  · exact g32p_supplierForest_actual_014675
  · exact g32p_supplierForest_actual_014709
  · exact g32p_supplierForest_actual_014767
  · exact g32p_supplierForest_actual_014778
  · exact g32p_supplierForest_actual_014782
  · exact g32p_supplierForest_actual_014785
  · exact g32p_supplierForest_actual_014792
  · exact g32p_supplierForest_actual_014802
  · exact g32p_supplierForest_actual_014810
  · exact g32p_supplierForest_actual_014918
  · exact g32p_supplierForest_actual_014939
  · exact g32p_supplierForest_actual_014956
  · exact g32p_supplierForest_actual_014958
  · exact g32p_supplierForest_actual_014964
  · exact g32p_supplierForest_actual_014967
  · exact g32p_supplierForest_actual_014980
  · exact g32p_supplierForest_actual_014982
  · exact g32p_supplierForest_actual_015023
  · exact g32p_supplierForest_actual_015056
  · exact g32p_supplierForest_actual_015062
  · exact g32p_supplierForest_actual_015134
  · exact g32p_supplierForest_actual_015176
  · exact g32p_supplierForest_actual_015187
  · exact g32p_supplierForest_actual_015236
  · exact g32p_supplierForest_actual_015267
  · exact g32p_supplierForest_actual_015436
  · exact g32p_supplierForest_actual_015438
  · exact g32p_supplierForest_actual_015474
  · exact g32p_supplierForest_actual_015477
  · exact g32p_supplierForest_actual_015487
  · exact g32p_supplierForest_actual_015524
  · exact g32p_supplierForest_actual_015539
  · exact g32p_supplierForest_actual_015555
  · exact g32p_supplierForest_actual_015558
  · exact g32p_supplierForest_actual_015571
  · exact g32p_supplierForest_actual_015584
  · exact g32p_supplierForest_actual_015594
  · exact g32p_supplierForest_actual_015608
  · exact g32p_supplierForest_actual_015677
  · exact g32p_supplierForest_actual_015694
  · exact g32p_supplierForest_actual_015721
  · exact g32p_supplierForest_actual_015734
  · exact g32p_supplierForest_actual_015741
  · exact g32p_supplierForest_actual_015764
  · exact g32p_supplierForest_actual_015797
  · exact g32p_supplierForest_actual_015834
  · exact g32p_supplierForest_actual_015898
  · exact g32p_supplierForest_actual_015907
  · exact g32p_supplierForest_actual_015946
  · exact g32p_supplierForest_actual_015953
  · exact g32p_supplierForest_actual_015964
  · exact g32p_supplierForest_actual_015978
  · exact g32p_supplierForest_actual_015984
  · exact g32p_supplierForest_actual_015993
  · exact g32p_supplierForest_actual_015995
  · exact g32p_supplierForest_actual_016039
  · exact g32p_supplierForest_actual_016040
  · exact g32p_supplierForest_actual_016080
  · exact g32p_supplierForest_actual_016123
  · exact g32p_supplierForest_actual_016171
  · exact g32p_supplierForest_actual_016181
  · exact g32p_supplierForest_actual_016216
  · exact g32p_supplierForest_actual_016228
  · exact g32p_supplierForest_actual_016244
  · exact g32p_supplierForest_actual_016266
  · exact g32p_supplierForest_actual_016283
  · exact g32p_supplierForest_actual_016289
  · exact g32p_supplierForest_actual_016291
  · exact g32p_supplierForest_actual_016307
  · exact g32p_supplierForest_actual_016368
  · exact g32p_supplierForest_actual_016372
  · exact g32p_supplierForest_actual_016373
  · exact g32p_supplierForest_actual_016384
  · exact g32p_supplierForest_actual_016393
  · exact g32p_supplierForest_actual_016398
  · exact g32p_supplierForest_actual_016432
  · exact g32p_supplierForest_actual_016434
  · exact g32p_supplierForest_actual_016437
  · exact g32p_supplierForest_actual_016440
  · exact g32p_supplierForest_actual_016491
  · exact g32p_supplierForest_actual_016526
  · exact g32p_supplierForest_actual_016536
  · exact g32p_supplierForest_actual_016572
  · exact g32p_supplierForest_actual_016600
  · exact g32p_supplierForest_actual_016613
  · exact g32p_supplierForest_actual_016619
  · exact g32p_supplierForest_actual_016628
  · exact g32p_supplierForest_actual_016650
  · exact g32p_supplierForest_actual_016652
  · exact g32p_supplierForest_actual_016663
  · exact g32p_supplierForest_actual_016673
  · exact g32p_supplierForest_actual_016721
  · exact g32p_supplierForest_actual_016740
  · exact g32p_supplierForest_actual_016814
  · exact g32p_supplierForest_actual_016827
  · exact g32p_supplierForest_actual_016829
  · exact g32p_supplierForest_actual_016847
  · exact g32p_supplierForest_actual_016853
  · exact g32p_supplierForest_actual_016893
  · exact g32p_supplierForest_actual_016934
  · exact g32p_supplierForest_actual_017022
  · exact g32p_supplierForest_actual_017024
  · exact g32p_supplierForest_actual_017168
  · exact g32p_supplierForest_actual_017220
  · exact g32p_supplierForest_actual_017226
  · exact g32p_supplierForest_actual_017232
  · exact g32p_supplierForest_actual_017236
  · exact g32p_supplierForest_actual_017324
  · exact g32p_supplierForest_actual_017335
  · exact g32p_supplierForest_actual_017336
  · exact g32p_supplierForest_actual_017401
  · exact g32p_supplierForest_actual_017457
  · exact g32p_supplierForest_actual_017460
  · exact g32p_supplierForest_actual_017510
  · exact g32p_supplierForest_actual_017523
  · exact g32p_supplierForest_actual_017582
  · exact g32p_supplierForest_actual_017591
  · exact g32p_supplierForest_actual_017592
  · exact g32p_supplierForest_actual_017706
  · exact g32p_supplierForest_actual_017716
  · exact g32p_supplierForest_actual_017762
  · exact g32p_supplierForest_actual_017777
  · exact g32p_supplierForest_actual_017807
  · exact g32p_supplierForest_actual_017849
  · exact g32p_supplierForest_actual_017851
  · exact g32p_supplierForest_actual_017888
  · exact g32p_supplierForest_actual_017890
  · exact g32p_supplierForest_actual_017902
  · exact g32p_supplierForest_actual_017915
  · exact g32p_supplierForest_actual_017962
  · exact g32p_supplierForest_actual_018006
  · exact g32p_supplierForest_actual_018034
  · exact g32p_supplierForest_actual_018038
  · exact g32p_supplierForest_actual_018080
  · exact g32p_supplierForest_actual_018108
  · exact g32p_supplierForest_actual_018141
  · exact g32p_supplierForest_actual_018228
  · exact g32p_supplierForest_actual_018251
  · exact g32p_supplierForest_actual_018303
  · exact g32p_supplierForest_actual_018357
  · exact g32p_supplierForest_actual_018358
  · exact g32p_supplierForest_actual_018362
  · exact g32p_supplierForest_actual_018410
  · exact g32p_supplierForest_actual_018423
  · exact g32p_supplierForest_actual_018486
  · exact g32p_supplierForest_actual_018501
  · exact g32p_supplierForest_actual_018502
  · exact g32p_supplierForest_actual_018518
  · exact g32p_supplierForest_actual_018520
  · exact g32p_supplierForest_actual_018530
  · exact g32p_supplierForest_actual_018536
  · exact g32p_supplierForest_actual_018567
  · exact g32p_supplierForest_actual_018579
  · exact g32p_supplierForest_actual_018586
  · exact g32p_supplierForest_actual_018603
  · exact g32p_supplierForest_actual_018608
  · exact g32p_supplierForest_actual_018619
  · exact g32p_supplierForest_actual_018623
  · exact g32p_supplierForest_actual_018626
  · exact g32p_supplierForest_actual_018636
  · exact g32p_supplierForest_actual_018639
  · exact g32p_supplierForest_actual_018668
  · exact g32p_supplierForest_actual_018709
  · exact g32p_supplierForest_actual_018765
  · exact g32p_supplierForest_actual_018776
  · exact g32p_supplierForest_actual_018894
  · exact g32p_supplierForest_actual_018950
  · exact g32p_supplierForest_actual_018981
  · exact g32p_supplierForest_actual_018983
  · exact g32p_supplierForest_actual_018984
  · exact g32p_supplierForest_actual_019019
  · exact g32p_supplierForest_actual_019059
  · exact g32p_supplierForest_actual_019070
  · exact g32p_supplierForest_actual_019077
  · exact g32p_supplierForest_actual_019078
  · exact g32p_supplierForest_actual_019178
  · exact g32p_supplierForest_actual_019197
  · exact g32p_supplierForest_actual_019199
  · exact g32p_supplierForest_actual_019208
  · exact g32p_supplierForest_actual_019214
  · exact g32p_supplierForest_actual_019233
  · exact g32p_supplierForest_actual_019244
  · exact g32p_supplierForest_actual_019275
  · exact g32p_supplierForest_actual_019376
  · exact g32p_supplierForest_actual_019378
  · exact g32p_supplierForest_actual_019397
  · exact g32p_supplierForest_actual_019420
  · exact g32p_supplierForest_actual_019444
  · exact g32p_supplierForest_actual_019522
  · exact g32p_supplierForest_actual_019535
  · exact g32p_supplierForest_actual_019562
  · exact g32p_supplierForest_actual_019581
  · exact g32p_supplierForest_actual_019584
  · exact g32p_supplierForest_actual_019611
  · exact g32p_supplierForest_actual_019636
  · exact g32p_supplierForest_actual_019732
  · exact g32p_supplierForest_actual_019794
  · exact g32p_supplierForest_actual_019796
  · exact g32p_supplierForest_actual_019824
  · exact g32p_supplierForest_actual_019830
  · exact g32p_supplierForest_actual_019919
  · exact g32p_supplierForest_actual_019930
  · exact g32p_supplierForest_actual_019938
  · exact g32p_supplierForest_actual_019952
  · exact g32p_supplierForest_actual_019995
  · exact g32p_supplierForest_actual_020012
  · exact g32p_supplierForest_actual_020044
  · exact g32p_supplierForest_actual_020070
  · exact g32p_supplierForest_actual_020071
  · exact g32p_supplierForest_actual_020091
  · exact g32p_supplierForest_actual_020126
  · exact g32p_supplierForest_actual_020173
  · exact g32p_supplierForest_actual_020180
  · exact g32p_supplierForest_actual_020191
  · exact g32p_supplierForest_actual_020192
  · exact g32p_supplierForest_actual_020216
  · exact g32p_supplierForest_actual_020230
  · exact g32p_supplierForest_actual_020241
  · exact g32p_supplierForest_actual_020264
  · exact g32p_supplierForest_actual_020293
  · exact g32p_supplierForest_actual_020310
  · exact g32p_supplierForest_actual_020335
  · exact g32p_supplierForest_actual_020338
  · exact g32p_supplierForest_actual_020363
  · exact g32p_supplierForest_actual_020384
  · exact g32p_supplierForest_actual_020395
  · exact g32p_supplierForest_actual_020397
  · exact g32p_supplierForest_actual_020402
  · exact g32p_supplierForest_actual_020409
  · exact g32p_supplierForest_actual_020414
  · exact g32p_supplierForest_actual_020452
  · exact g32p_supplierForest_actual_020459
  · exact g32p_supplierForest_actual_020490
  · exact g32p_supplierForest_actual_020506
  · exact g32p_supplierForest_actual_020542
  · exact g32p_supplierForest_actual_020563
  · exact g32p_supplierForest_actual_020569
  · exact g32p_supplierForest_actual_020573
  · exact g32p_supplierForest_actual_020581
  · exact g32p_supplierForest_actual_020607
  · exact g32p_supplierForest_actual_020618
  · exact g32p_supplierForest_actual_020625
  · exact g32p_supplierForest_actual_020660
  · exact g32p_supplierForest_actual_020663
  · exact g32p_supplierForest_actual_020667
  · exact g32p_supplierForest_actual_020669

def g32p_supplierForest_nodes_035 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_020709 else g32p_supplierForest_node_020790) else (if i.val < 3 then g32p_supplierForest_node_020821 else g32p_supplierForest_node_020825)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_020853 else g32p_supplierForest_node_020900) else (if i.val < 7 then g32p_supplierForest_node_020914 else g32p_supplierForest_node_020943))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_020955 else g32p_supplierForest_node_020958) else (if i.val < 11 then g32p_supplierForest_node_020959 else g32p_supplierForest_node_021042)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_021093 else g32p_supplierForest_node_021099) else (if i.val < 15 then g32p_supplierForest_node_021124 else g32p_supplierForest_node_021126)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_021193 else g32p_supplierForest_node_021199) else (if i.val < 19 then g32p_supplierForest_node_021222 else g32p_supplierForest_node_021242)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_021282 else g32p_supplierForest_node_021301) else (if i.val < 23 then g32p_supplierForest_node_021313 else g32p_supplierForest_node_021333))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_021336 else g32p_supplierForest_node_021479) else (if i.val < 27 then g32p_supplierForest_node_021496 else g32p_supplierForest_node_021535)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_021554 else g32p_supplierForest_node_021562) else (if i.val < 31 then g32p_supplierForest_node_021595 else g32p_supplierForest_node_021604))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_021605 else g32p_supplierForest_node_021628) else (if i.val < 35 then g32p_supplierForest_node_021684 else g32p_supplierForest_node_021692)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_021705 else g32p_supplierForest_node_021708) else (if i.val < 39 then g32p_supplierForest_node_021711 else g32p_supplierForest_node_021757))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_021797 else g32p_supplierForest_node_021853) else (if i.val < 43 then g32p_supplierForest_node_021871 else g32p_supplierForest_node_021909)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_021950 else g32p_supplierForest_node_021959) else (if i.val < 47 then g32p_supplierForest_node_022025 else g32p_supplierForest_node_022026)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_022137 else g32p_supplierForest_node_022186) else (if i.val < 51 then g32p_supplierForest_node_022190 else g32p_supplierForest_node_022217)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_022218 else g32p_supplierForest_node_022221) else (if i.val < 55 then g32p_supplierForest_node_022225 else g32p_supplierForest_node_022268))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_022278 else g32p_supplierForest_node_022298) else (if i.val < 59 then g32p_supplierForest_node_022299 else g32p_supplierForest_node_022303)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_022349 else g32p_supplierForest_node_022357) else (if i.val < 63 then g32p_supplierForest_node_022364 else g32p_supplierForest_node_022377)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_022386 else g32p_supplierForest_node_022393) else (if i.val < 67 then g32p_supplierForest_node_022432 else g32p_supplierForest_node_022435)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_022470 else g32p_supplierForest_node_022506) else (if i.val < 71 then g32p_supplierForest_node_022584 else g32p_supplierForest_node_022617))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_022633 else g32p_supplierForest_node_022635) else (if i.val < 75 then g32p_supplierForest_node_022641 else g32p_supplierForest_node_022645)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_022648 else g32p_supplierForest_node_022692) else (if i.val < 79 then g32p_supplierForest_node_022740 else g32p_supplierForest_node_022779)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_022800 else g32p_supplierForest_node_022810) else (if i.val < 83 then g32p_supplierForest_node_022824 else g32p_supplierForest_node_022835)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_022858 else g32p_supplierForest_node_022912) else (if i.val < 87 then g32p_supplierForest_node_022914 else g32p_supplierForest_node_022919))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_022922 else g32p_supplierForest_node_023024) else (if i.val < 91 then g32p_supplierForest_node_023054 else g32p_supplierForest_node_023068)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_023093 else g32p_supplierForest_node_023112) else (if i.val < 95 then g32p_supplierForest_node_023126 else g32p_supplierForest_node_023136))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_023177 else g32p_supplierForest_node_023221) else (if i.val < 99 then g32p_supplierForest_node_023249 else g32p_supplierForest_node_023256)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_023317 else g32p_supplierForest_node_023358) else (if i.val < 103 then g32p_supplierForest_node_023404 else g32p_supplierForest_node_023406))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_023427 else g32p_supplierForest_node_023456) else (if i.val < 107 then g32p_supplierForest_node_023498 else g32p_supplierForest_node_023505)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_023583 else g32p_supplierForest_node_023656) else (if i.val < 111 then g32p_supplierForest_node_023675 else g32p_supplierForest_node_023777)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_023788 else g32p_supplierForest_node_023822) else (if i.val < 115 then g32p_supplierForest_node_023861 else g32p_supplierForest_node_023865)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_023876 else g32p_supplierForest_node_023946) else (if i.val < 119 then g32p_supplierForest_node_023965 else g32p_supplierForest_node_023970))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_024032 else g32p_supplierForest_node_024052) else (if i.val < 123 then g32p_supplierForest_node_024085 else g32p_supplierForest_node_024089)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_024127 else g32p_supplierForest_node_024169) else (if i.val < 127 then g32p_supplierForest_node_024194 else g32p_supplierForest_node_024208))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_024218 else g32p_supplierForest_node_024228) else (if i.val < 131 then g32p_supplierForest_node_024262 else g32p_supplierForest_node_024279)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_024294 else g32p_supplierForest_node_024310) else (if i.val < 135 then g32p_supplierForest_node_024331 else g32p_supplierForest_node_024345))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_024359 else g32p_supplierForest_node_024364) else (if i.val < 139 then g32p_supplierForest_node_024368 else g32p_supplierForest_node_024376)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_024399 else g32p_supplierForest_node_024405) else (if i.val < 143 then g32p_supplierForest_node_024408 else g32p_supplierForest_node_024507)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_024509 else g32p_supplierForest_node_024511) else (if i.val < 147 then g32p_supplierForest_node_024582 else g32p_supplierForest_node_024615)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_024626 else g32p_supplierForest_node_024636) else (if i.val < 151 then g32p_supplierForest_node_024661 else g32p_supplierForest_node_024679))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_024726 else g32p_supplierForest_node_024728) else (if i.val < 155 then g32p_supplierForest_node_024733 else g32p_supplierForest_node_024773)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_024789 else g32p_supplierForest_node_024809) else (if i.val < 159 then g32p_supplierForest_node_024823 else g32p_supplierForest_node_024846))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_024861 else g32p_supplierForest_node_024868) else (if i.val < 163 then g32p_supplierForest_node_024926 else g32p_supplierForest_node_024944)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_024949 else g32p_supplierForest_node_024960) else (if i.val < 167 then g32p_supplierForest_node_024983 else g32p_supplierForest_node_024987))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_024991 else g32p_supplierForest_node_024992) else (if i.val < 171 then g32p_supplierForest_node_025002 else g32p_supplierForest_node_025006)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_025033 else g32p_supplierForest_node_025036) else (if i.val < 175 then g32p_supplierForest_node_025044 else g32p_supplierForest_node_025061)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_025072 else g32p_supplierForest_node_025077) else (if i.val < 179 then g32p_supplierForest_node_025104 else g32p_supplierForest_node_025140)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_025156 else g32p_supplierForest_node_025157) else (if i.val < 183 then g32p_supplierForest_node_025171 else g32p_supplierForest_node_025196))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_025245 else g32p_supplierForest_node_025263) else (if i.val < 187 then g32p_supplierForest_node_025276 else g32p_supplierForest_node_025383)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_025390 else g32p_supplierForest_node_025392) else (if i.val < 191 then g32p_supplierForest_node_025406 else g32p_supplierForest_node_025416)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_025454 else g32p_supplierForest_node_025485) else (if i.val < 195 then g32p_supplierForest_node_025489 else g32p_supplierForest_node_025499)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_025533 else g32p_supplierForest_node_025540) else (if i.val < 199 then g32p_supplierForest_node_025584 else g32p_supplierForest_node_025617))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_025625 else g32p_supplierForest_node_025632) else (if i.val < 203 then g32p_supplierForest_node_025647 else g32p_supplierForest_node_025650)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_025659 else g32p_supplierForest_node_025674) else (if i.val < 207 then g32p_supplierForest_node_025679 else g32p_supplierForest_node_025702)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_025718 else g32p_supplierForest_node_025726) else (if i.val < 211 then g32p_supplierForest_node_025730 else g32p_supplierForest_node_025744)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_025768 else g32p_supplierForest_node_025793) else (if i.val < 215 then g32p_supplierForest_node_025797 else g32p_supplierForest_node_025811))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_025843 else g32p_supplierForest_node_025862) else (if i.val < 219 then g32p_supplierForest_node_025864 else g32p_supplierForest_node_025883)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_025887 else g32p_supplierForest_node_025891) else (if i.val < 223 then g32p_supplierForest_node_025916 else g32p_supplierForest_node_025923))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_025940 else g32p_supplierForest_node_025979) else (if i.val < 227 then g32p_supplierForest_node_025997 else g32p_supplierForest_node_026070)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_026084 else g32p_supplierForest_node_026117) else (if i.val < 231 then g32p_supplierForest_node_026136 else g32p_supplierForest_node_026138))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_026140 else g32p_supplierForest_node_026172) else (if i.val < 235 then g32p_supplierForest_node_026182 else g32p_supplierForest_node_026190)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_026191 else g32p_supplierForest_node_026196) else (if i.val < 239 then g32p_supplierForest_node_026201 else g32p_supplierForest_node_026210)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_026216 else g32p_supplierForest_node_026219) else (if i.val < 243 then g32p_supplierForest_node_026225 else g32p_supplierForest_node_026261)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_026274 else g32p_supplierForest_node_026275) else (if i.val < 247 then g32p_supplierForest_node_026295 else g32p_supplierForest_node_026334))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_026342 else g32p_supplierForest_node_026390) else (if i.val < 251 then g32p_supplierForest_node_026409 else g32p_supplierForest_node_026449)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_026461 else g32p_supplierForest_node_026469) else (if i.val < 255 then g32p_supplierForest_node_026486 else g32p_supplierForest_node_026487))))))))

def g32p_supplierForest_classes_035 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 49 else 27) else (if i.val < 3 then 10 else 51)) else (if i.val < 6 then (if i.val < 5 then 26 else 25) else (if i.val < 7 then 13 else 9))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 12 else 48) else (if i.val < 11 then 9 else 49)) else (if i.val < 14 then (if i.val < 13 then 26 else 13) else (if i.val < 15 then 12 else 12)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 13 else 27) else (if i.val < 19 then 13 else 47)) else (if i.val < 22 then (if i.val < 21 then 49 else 48) else (if i.val < 23 then 25 else 51))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 49) else (if i.val < 27 then 49 else 48)) else (if i.val < 30 then (if i.val < 29 then 25 else 12) else (if i.val < 31 then 49 else 13))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 25 else 47) else (if i.val < 35 then 12 else 25)) else (if i.val < 38 then (if i.val < 37 then 9 else 48) else (if i.val < 39 then 13 else 12))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 47 else 10) else (if i.val < 43 then 49 else 26)) else (if i.val < 46 then (if i.val < 45 then 49 else 27) else (if i.val < 47 then 9 else 9)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 48) else (if i.val < 51 then 48 else 47)) else (if i.val < 54 then (if i.val < 53 then 10 else 51) else (if i.val < 55 then 50 else 12))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 50 else 48) else (if i.val < 59 then 26 else 10)) else (if i.val < 62 then (if i.val < 61 then 49 else 49) else (if i.val < 63 then 13 else 47)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 48 else 49) else (if i.val < 67 then 25 else 13)) else (if i.val < 70 then (if i.val < 69 then 26 else 13) else (if i.val < 71 then 9 else 49))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 10 else 9) else (if i.val < 75 then 49 else 49)) else (if i.val < 78 then (if i.val < 77 then 13 else 12) else (if i.val < 79 then 13 else 50)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 13 else 25) else (if i.val < 83 then 10 else 26)) else (if i.val < 86 then (if i.val < 85 then 13 else 49) else (if i.val < 87 then 25 else 25))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 26 else 27) else (if i.val < 91 then 10 else 26)) else (if i.val < 94 then (if i.val < 93 then 12 else 27) else (if i.val < 95 then 47 else 12))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 48 else 10) else (if i.val < 99 then 27 else 13)) else (if i.val < 102 then (if i.val < 101 then 9 else 8) else (if i.val < 103 then 27 else 47))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 10 else 49) else (if i.val < 107 then 49 else 49)) else (if i.val < 110 then (if i.val < 109 then 48 else 48) else (if i.val < 111 then 47 else 50)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 10 else 51) else (if i.val < 115 then 51 else 50)) else (if i.val < 118 then (if i.val < 117 then 26 else 10) else (if i.val < 119 then 27 else 51))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 48 else 47) else (if i.val < 123 then 49 else 12)) else (if i.val < 126 then (if i.val < 125 then 46 else 11) else (if i.val < 127 then 13 else 26))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 46) else (if i.val < 131 then 26 else 8)) else (if i.val < 134 then (if i.val < 133 then 49 else 49) else (if i.val < 135 then 50 else 9))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 26 else 10) else (if i.val < 139 then 50 else 25)) else (if i.val < 142 then (if i.val < 141 then 50 else 50) else (if i.val < 143 then 48 else 16)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 16 else 30) else (if i.val < 147 then 31 else 36)) else (if i.val < 150 then (if i.val < 149 then 15 else 34) else (if i.val < 151 then 32 else 34))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 34 else 57) else (if i.val < 155 then 59 else 31)) else (if i.val < 158 then (if i.val < 157 then 30 else 30) else (if i.val < 159 then 57 else 33))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 32 else 31) else (if i.val < 163 then 16 else 17)) else (if i.val < 166 then (if i.val < 165 then 57 else 3) else (if i.val < 167 then 57 else 31))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 16 else 4) else (if i.val < 171 then 17 else 64)) else (if i.val < 174 then (if i.val < 173 then 57 else 61) else (if i.val < 175 then 15 else 58)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 57 else 57) else (if i.val < 179 then 57 else 17)) else (if i.val < 182 then (if i.val < 181 then 3 else 57) else (if i.val < 183 then 33 else 30))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 34 else 17) else (if i.val < 187 then 57 else 30)) else (if i.val < 190 then (if i.val < 189 then 30 else 17) else (if i.val < 191 then 30 else 4)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 4 else 34) else (if i.val < 195 then 2 else 16)) else (if i.val < 198 then (if i.val < 197 then 16 else 34) else (if i.val < 199 then 34 else 16))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 30 else 4) else (if i.val < 203 then 15 else 3)) else (if i.val < 206 then (if i.val < 205 then 29 else 15) else (if i.val < 207 then 15 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 31 else 14) else (if i.val < 211 then 57 else 30)) else (if i.val < 214 then (if i.val < 213 then 3 else 57) else (if i.val < 215 then 16 else 30))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 32) else (if i.val < 219 then 16 else 4)) else (if i.val < 222 then (if i.val < 221 then 30 else 16) else (if i.val < 223 then 59 else 34))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 4) else (if i.val < 227 then 32 else 16)) else (if i.val < 230 then (if i.val < 229 then 30 else 64) else (if i.val < 231 then 16 else 4))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 16 else 58) else (if i.val < 235 then 34 else 15)) else (if i.val < 238 then (if i.val < 237 then 2 else 33) else (if i.val < 239 then 62 else 14)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 30 else 59) else (if i.val < 243 then 34 else 15)) else (if i.val < 246 then (if i.val < 245 then 30 else 57) else (if i.val < 247 then 16 else 65))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 64 else 32) else (if i.val < 251 then 14 else 34)) else (if i.val < 254 then (if i.val < 253 then 58 else 57) else (if i.val < 255 then 57 else 4))))))))

theorem g32p_supplierForest_actual_035 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_035 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_035 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_020709
  · exact g32p_supplierForest_actual_020790
  · exact g32p_supplierForest_actual_020821
  · exact g32p_supplierForest_actual_020825
  · exact g32p_supplierForest_actual_020853
  · exact g32p_supplierForest_actual_020900
  · exact g32p_supplierForest_actual_020914
  · exact g32p_supplierForest_actual_020943
  · exact g32p_supplierForest_actual_020955
  · exact g32p_supplierForest_actual_020958
  · exact g32p_supplierForest_actual_020959
  · exact g32p_supplierForest_actual_021042
  · exact g32p_supplierForest_actual_021093
  · exact g32p_supplierForest_actual_021099
  · exact g32p_supplierForest_actual_021124
  · exact g32p_supplierForest_actual_021126
  · exact g32p_supplierForest_actual_021193
  · exact g32p_supplierForest_actual_021199
  · exact g32p_supplierForest_actual_021222
  · exact g32p_supplierForest_actual_021242
  · exact g32p_supplierForest_actual_021282
  · exact g32p_supplierForest_actual_021301
  · exact g32p_supplierForest_actual_021313
  · exact g32p_supplierForest_actual_021333
  · exact g32p_supplierForest_actual_021336
  · exact g32p_supplierForest_actual_021479
  · exact g32p_supplierForest_actual_021496
  · exact g32p_supplierForest_actual_021535
  · exact g32p_supplierForest_actual_021554
  · exact g32p_supplierForest_actual_021562
  · exact g32p_supplierForest_actual_021595
  · exact g32p_supplierForest_actual_021604
  · exact g32p_supplierForest_actual_021605
  · exact g32p_supplierForest_actual_021628
  · exact g32p_supplierForest_actual_021684
  · exact g32p_supplierForest_actual_021692
  · exact g32p_supplierForest_actual_021705
  · exact g32p_supplierForest_actual_021708
  · exact g32p_supplierForest_actual_021711
  · exact g32p_supplierForest_actual_021757
  · exact g32p_supplierForest_actual_021797
  · exact g32p_supplierForest_actual_021853
  · exact g32p_supplierForest_actual_021871
  · exact g32p_supplierForest_actual_021909
  · exact g32p_supplierForest_actual_021950
  · exact g32p_supplierForest_actual_021959
  · exact g32p_supplierForest_actual_022025
  · exact g32p_supplierForest_actual_022026
  · exact g32p_supplierForest_actual_022137
  · exact g32p_supplierForest_actual_022186
  · exact g32p_supplierForest_actual_022190
  · exact g32p_supplierForest_actual_022217
  · exact g32p_supplierForest_actual_022218
  · exact g32p_supplierForest_actual_022221
  · exact g32p_supplierForest_actual_022225
  · exact g32p_supplierForest_actual_022268
  · exact g32p_supplierForest_actual_022278
  · exact g32p_supplierForest_actual_022298
  · exact g32p_supplierForest_actual_022299
  · exact g32p_supplierForest_actual_022303
  · exact g32p_supplierForest_actual_022349
  · exact g32p_supplierForest_actual_022357
  · exact g32p_supplierForest_actual_022364
  · exact g32p_supplierForest_actual_022377
  · exact g32p_supplierForest_actual_022386
  · exact g32p_supplierForest_actual_022393
  · exact g32p_supplierForest_actual_022432
  · exact g32p_supplierForest_actual_022435
  · exact g32p_supplierForest_actual_022470
  · exact g32p_supplierForest_actual_022506
  · exact g32p_supplierForest_actual_022584
  · exact g32p_supplierForest_actual_022617
  · exact g32p_supplierForest_actual_022633
  · exact g32p_supplierForest_actual_022635
  · exact g32p_supplierForest_actual_022641
  · exact g32p_supplierForest_actual_022645
  · exact g32p_supplierForest_actual_022648
  · exact g32p_supplierForest_actual_022692
  · exact g32p_supplierForest_actual_022740
  · exact g32p_supplierForest_actual_022779
  · exact g32p_supplierForest_actual_022800
  · exact g32p_supplierForest_actual_022810
  · exact g32p_supplierForest_actual_022824
  · exact g32p_supplierForest_actual_022835
  · exact g32p_supplierForest_actual_022858
  · exact g32p_supplierForest_actual_022912
  · exact g32p_supplierForest_actual_022914
  · exact g32p_supplierForest_actual_022919
  · exact g32p_supplierForest_actual_022922
  · exact g32p_supplierForest_actual_023024
  · exact g32p_supplierForest_actual_023054
  · exact g32p_supplierForest_actual_023068
  · exact g32p_supplierForest_actual_023093
  · exact g32p_supplierForest_actual_023112
  · exact g32p_supplierForest_actual_023126
  · exact g32p_supplierForest_actual_023136
  · exact g32p_supplierForest_actual_023177
  · exact g32p_supplierForest_actual_023221
  · exact g32p_supplierForest_actual_023249
  · exact g32p_supplierForest_actual_023256
  · exact g32p_supplierForest_actual_023317
  · exact g32p_supplierForest_actual_023358
  · exact g32p_supplierForest_actual_023404
  · exact g32p_supplierForest_actual_023406
  · exact g32p_supplierForest_actual_023427
  · exact g32p_supplierForest_actual_023456
  · exact g32p_supplierForest_actual_023498
  · exact g32p_supplierForest_actual_023505
  · exact g32p_supplierForest_actual_023583
  · exact g32p_supplierForest_actual_023656
  · exact g32p_supplierForest_actual_023675
  · exact g32p_supplierForest_actual_023777
  · exact g32p_supplierForest_actual_023788
  · exact g32p_supplierForest_actual_023822
  · exact g32p_supplierForest_actual_023861
  · exact g32p_supplierForest_actual_023865
  · exact g32p_supplierForest_actual_023876
  · exact g32p_supplierForest_actual_023946
  · exact g32p_supplierForest_actual_023965
  · exact g32p_supplierForest_actual_023970
  · exact g32p_supplierForest_actual_024032
  · exact g32p_supplierForest_actual_024052
  · exact g32p_supplierForest_actual_024085
  · exact g32p_supplierForest_actual_024089
  · exact g32p_supplierForest_actual_024127
  · exact g32p_supplierForest_actual_024169
  · exact g32p_supplierForest_actual_024194
  · exact g32p_supplierForest_actual_024208
  · exact g32p_supplierForest_actual_024218
  · exact g32p_supplierForest_actual_024228
  · exact g32p_supplierForest_actual_024262
  · exact g32p_supplierForest_actual_024279
  · exact g32p_supplierForest_actual_024294
  · exact g32p_supplierForest_actual_024310
  · exact g32p_supplierForest_actual_024331
  · exact g32p_supplierForest_actual_024345
  · exact g32p_supplierForest_actual_024359
  · exact g32p_supplierForest_actual_024364
  · exact g32p_supplierForest_actual_024368
  · exact g32p_supplierForest_actual_024376
  · exact g32p_supplierForest_actual_024399
  · exact g32p_supplierForest_actual_024405
  · exact g32p_supplierForest_actual_024408
  · exact g32p_supplierForest_actual_024507
  · exact g32p_supplierForest_actual_024509
  · exact g32p_supplierForest_actual_024511
  · exact g32p_supplierForest_actual_024582
  · exact g32p_supplierForest_actual_024615
  · exact g32p_supplierForest_actual_024626
  · exact g32p_supplierForest_actual_024636
  · exact g32p_supplierForest_actual_024661
  · exact g32p_supplierForest_actual_024679
  · exact g32p_supplierForest_actual_024726
  · exact g32p_supplierForest_actual_024728
  · exact g32p_supplierForest_actual_024733
  · exact g32p_supplierForest_actual_024773
  · exact g32p_supplierForest_actual_024789
  · exact g32p_supplierForest_actual_024809
  · exact g32p_supplierForest_actual_024823
  · exact g32p_supplierForest_actual_024846
  · exact g32p_supplierForest_actual_024861
  · exact g32p_supplierForest_actual_024868
  · exact g32p_supplierForest_actual_024926
  · exact g32p_supplierForest_actual_024944
  · exact g32p_supplierForest_actual_024949
  · exact g32p_supplierForest_actual_024960
  · exact g32p_supplierForest_actual_024983
  · exact g32p_supplierForest_actual_024987
  · exact g32p_supplierForest_actual_024991
  · exact g32p_supplierForest_actual_024992
  · exact g32p_supplierForest_actual_025002
  · exact g32p_supplierForest_actual_025006
  · exact g32p_supplierForest_actual_025033
  · exact g32p_supplierForest_actual_025036
  · exact g32p_supplierForest_actual_025044
  · exact g32p_supplierForest_actual_025061
  · exact g32p_supplierForest_actual_025072
  · exact g32p_supplierForest_actual_025077
  · exact g32p_supplierForest_actual_025104
  · exact g32p_supplierForest_actual_025140
  · exact g32p_supplierForest_actual_025156
  · exact g32p_supplierForest_actual_025157
  · exact g32p_supplierForest_actual_025171
  · exact g32p_supplierForest_actual_025196
  · exact g32p_supplierForest_actual_025245
  · exact g32p_supplierForest_actual_025263
  · exact g32p_supplierForest_actual_025276
  · exact g32p_supplierForest_actual_025383
  · exact g32p_supplierForest_actual_025390
  · exact g32p_supplierForest_actual_025392
  · exact g32p_supplierForest_actual_025406
  · exact g32p_supplierForest_actual_025416
  · exact g32p_supplierForest_actual_025454
  · exact g32p_supplierForest_actual_025485
  · exact g32p_supplierForest_actual_025489
  · exact g32p_supplierForest_actual_025499
  · exact g32p_supplierForest_actual_025533
  · exact g32p_supplierForest_actual_025540
  · exact g32p_supplierForest_actual_025584
  · exact g32p_supplierForest_actual_025617
  · exact g32p_supplierForest_actual_025625
  · exact g32p_supplierForest_actual_025632
  · exact g32p_supplierForest_actual_025647
  · exact g32p_supplierForest_actual_025650
  · exact g32p_supplierForest_actual_025659
  · exact g32p_supplierForest_actual_025674
  · exact g32p_supplierForest_actual_025679
  · exact g32p_supplierForest_actual_025702
  · exact g32p_supplierForest_actual_025718
  · exact g32p_supplierForest_actual_025726
  · exact g32p_supplierForest_actual_025730
  · exact g32p_supplierForest_actual_025744
  · exact g32p_supplierForest_actual_025768
  · exact g32p_supplierForest_actual_025793
  · exact g32p_supplierForest_actual_025797
  · exact g32p_supplierForest_actual_025811
  · exact g32p_supplierForest_actual_025843
  · exact g32p_supplierForest_actual_025862
  · exact g32p_supplierForest_actual_025864
  · exact g32p_supplierForest_actual_025883
  · exact g32p_supplierForest_actual_025887
  · exact g32p_supplierForest_actual_025891
  · exact g32p_supplierForest_actual_025916
  · exact g32p_supplierForest_actual_025923
  · exact g32p_supplierForest_actual_025940
  · exact g32p_supplierForest_actual_025979
  · exact g32p_supplierForest_actual_025997
  · exact g32p_supplierForest_actual_026070
  · exact g32p_supplierForest_actual_026084
  · exact g32p_supplierForest_actual_026117
  · exact g32p_supplierForest_actual_026136
  · exact g32p_supplierForest_actual_026138
  · exact g32p_supplierForest_actual_026140
  · exact g32p_supplierForest_actual_026172
  · exact g32p_supplierForest_actual_026182
  · exact g32p_supplierForest_actual_026190
  · exact g32p_supplierForest_actual_026191
  · exact g32p_supplierForest_actual_026196
  · exact g32p_supplierForest_actual_026201
  · exact g32p_supplierForest_actual_026210
  · exact g32p_supplierForest_actual_026216
  · exact g32p_supplierForest_actual_026219
  · exact g32p_supplierForest_actual_026225
  · exact g32p_supplierForest_actual_026261
  · exact g32p_supplierForest_actual_026274
  · exact g32p_supplierForest_actual_026275
  · exact g32p_supplierForest_actual_026295
  · exact g32p_supplierForest_actual_026334
  · exact g32p_supplierForest_actual_026342
  · exact g32p_supplierForest_actual_026390
  · exact g32p_supplierForest_actual_026409
  · exact g32p_supplierForest_actual_026449
  · exact g32p_supplierForest_actual_026461
  · exact g32p_supplierForest_actual_026469
  · exact g32p_supplierForest_actual_026486
  · exact g32p_supplierForest_actual_026487

def g32p_supplierForest_nodes_036 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_026489 else g32p_supplierForest_node_026560) else (if i.val < 3 then g32p_supplierForest_node_026655 else g32p_supplierForest_node_026692)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_026735 else g32p_supplierForest_node_026739) else (if i.val < 7 then g32p_supplierForest_node_026803 else g32p_supplierForest_node_026837))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_026857 else g32p_supplierForest_node_026867) else (if i.val < 11 then g32p_supplierForest_node_026872 else g32p_supplierForest_node_026905)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_026921 else g32p_supplierForest_node_026968) else (if i.val < 15 then g32p_supplierForest_node_026986 else g32p_supplierForest_node_026990)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_027046 else g32p_supplierForest_node_027051) else (if i.val < 19 then g32p_supplierForest_node_027099 else g32p_supplierForest_node_027106)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_027120 else g32p_supplierForest_node_027122) else (if i.val < 23 then g32p_supplierForest_node_027336 else g32p_supplierForest_node_027354))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_027403 else g32p_supplierForest_node_027430) else (if i.val < 27 then g32p_supplierForest_node_027432 else g32p_supplierForest_node_027438)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_027482 else g32p_supplierForest_node_027489) else (if i.val < 31 then g32p_supplierForest_node_027498 else g32p_supplierForest_node_027521))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_027569 else g32p_supplierForest_node_027576) else (if i.val < 35 then g32p_supplierForest_node_027659 else g32p_supplierForest_node_027661)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_027684 else g32p_supplierForest_node_027689) else (if i.val < 39 then g32p_supplierForest_node_027713 else g32p_supplierForest_node_027743))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_027755 else g32p_supplierForest_node_027757) else (if i.val < 43 then g32p_supplierForest_node_027771 else g32p_supplierForest_node_027782)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_027785 else g32p_supplierForest_node_027944) else (if i.val < 47 then g32p_supplierForest_node_027986 else g32p_supplierForest_node_027987)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_028001 else g32p_supplierForest_node_028015) else (if i.val < 51 then g32p_supplierForest_node_028020 else g32p_supplierForest_node_028066)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_028108 else g32p_supplierForest_node_028131) else (if i.val < 55 then g32p_supplierForest_node_028136 else g32p_supplierForest_node_028176))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_028184 else g32p_supplierForest_node_028208) else (if i.val < 59 then g32p_supplierForest_node_028228 else g32p_supplierForest_node_028229)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_028241 else g32p_supplierForest_node_028275) else (if i.val < 63 then g32p_supplierForest_node_028298 else g32p_supplierForest_node_028305)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_028308 else g32p_supplierForest_node_028343) else (if i.val < 67 then g32p_supplierForest_node_028364 else g32p_supplierForest_node_028376)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_028393 else g32p_supplierForest_node_028425) else (if i.val < 71 then g32p_supplierForest_node_028429 else g32p_supplierForest_node_028445))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_028452 else g32p_supplierForest_node_028463) else (if i.val < 75 then g32p_supplierForest_node_028470 else g32p_supplierForest_node_028476)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_028483 else g32p_supplierForest_node_028488) else (if i.val < 79 then g32p_supplierForest_node_028512 else g32p_supplierForest_node_028513)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_028517 else g32p_supplierForest_node_028545) else (if i.val < 83 then g32p_supplierForest_node_028560 else g32p_supplierForest_node_028567)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_028581 else g32p_supplierForest_node_028582) else (if i.val < 87 then g32p_supplierForest_node_028583 else g32p_supplierForest_node_028594))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_028642 else g32p_supplierForest_node_028677) else (if i.val < 91 then g32p_supplierForest_node_028682 else g32p_supplierForest_node_028694)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_028728 else g32p_supplierForest_node_028731) else (if i.val < 95 then g32p_supplierForest_node_028737 else g32p_supplierForest_node_028739))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_028744 else g32p_supplierForest_node_028758) else (if i.val < 99 then g32p_supplierForest_node_028790 else g32p_supplierForest_node_028795)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_028815 else g32p_supplierForest_node_028836) else (if i.val < 103 then g32p_supplierForest_node_028874 else g32p_supplierForest_node_028876))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_028925 else g32p_supplierForest_node_028940) else (if i.val < 107 then g32p_supplierForest_node_028971 else g32p_supplierForest_node_028973)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_029016 else g32p_supplierForest_node_029058) else (if i.val < 111 then g32p_supplierForest_node_029069 else g32p_supplierForest_node_029072)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_029075 else g32p_supplierForest_node_029094) else (if i.val < 115 then g32p_supplierForest_node_029095 else g32p_supplierForest_node_029138)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_029143 else g32p_supplierForest_node_029184) else (if i.val < 119 then g32p_supplierForest_node_029207 else g32p_supplierForest_node_029228))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_029231 else g32p_supplierForest_node_029232) else (if i.val < 123 then g32p_supplierForest_node_029249 else g32p_supplierForest_node_029268)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_029333 else g32p_supplierForest_node_029344) else (if i.val < 127 then g32p_supplierForest_node_029359 else g32p_supplierForest_node_029366))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_029378 else g32p_supplierForest_node_029406) else (if i.val < 131 then g32p_supplierForest_node_029415 else g32p_supplierForest_node_029433)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_029437 else g32p_supplierForest_node_029448) else (if i.val < 135 then g32p_supplierForest_node_029458 else g32p_supplierForest_node_029466))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_029499 else g32p_supplierForest_node_029505) else (if i.val < 139 then g32p_supplierForest_node_029514 else g32p_supplierForest_node_029526)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_029528 else g32p_supplierForest_node_029568) else (if i.val < 143 then g32p_supplierForest_node_029569 else g32p_supplierForest_node_029601)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_029647 else g32p_supplierForest_node_029719) else (if i.val < 147 then g32p_supplierForest_node_029771 else g32p_supplierForest_node_029776)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_029777 else g32p_supplierForest_node_029800) else (if i.val < 151 then g32p_supplierForest_node_029839 else g32p_supplierForest_node_029862))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_029883 else g32p_supplierForest_node_029925) else (if i.val < 155 then g32p_supplierForest_node_029928 else g32p_supplierForest_node_029951)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_029962 else g32p_supplierForest_node_029986) else (if i.val < 159 then g32p_supplierForest_node_030036 else g32p_supplierForest_node_030080))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_030087 else g32p_supplierForest_node_030107) else (if i.val < 163 then g32p_supplierForest_node_030118 else g32p_supplierForest_node_030122)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_030136 else g32p_supplierForest_node_030145) else (if i.val < 167 then g32p_supplierForest_node_030175 else g32p_supplierForest_node_030196))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_030205 else g32p_supplierForest_node_030211) else (if i.val < 171 then g32p_supplierForest_node_030248 else g32p_supplierForest_node_030252)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_030254 else g32p_supplierForest_node_030268) else (if i.val < 175 then g32p_supplierForest_node_030271 else g32p_supplierForest_node_030283)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_030323 else g32p_supplierForest_node_030355) else (if i.val < 179 then g32p_supplierForest_node_030415 else g32p_supplierForest_node_030433)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_030472 else g32p_supplierForest_node_030487) else (if i.val < 183 then g32p_supplierForest_node_030505 else g32p_supplierForest_node_030547))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_030578 else g32p_supplierForest_node_030597) else (if i.val < 187 then g32p_supplierForest_node_030600 else g32p_supplierForest_node_030608)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_030617 else g32p_supplierForest_node_030629) else (if i.val < 191 then g32p_supplierForest_node_030650 else g32p_supplierForest_node_030653)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_030659 else g32p_supplierForest_node_030686) else (if i.val < 195 then g32p_supplierForest_node_030741 else g32p_supplierForest_node_030780)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_030781 else g32p_supplierForest_node_030787) else (if i.val < 199 then g32p_supplierForest_node_030903 else g32p_supplierForest_node_030918))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_030964 else g32p_supplierForest_node_031001) else (if i.val < 203 then g32p_supplierForest_node_031003 else g32p_supplierForest_node_031131)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_031138 else g32p_supplierForest_node_031150) else (if i.val < 207 then g32p_supplierForest_node_031152 else g32p_supplierForest_node_031153)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_031226 else g32p_supplierForest_node_031233) else (if i.val < 211 then g32p_supplierForest_node_031250 else g32p_supplierForest_node_031266)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_031280 else g32p_supplierForest_node_031282) else (if i.val < 215 then g32p_supplierForest_node_031358 else g32p_supplierForest_node_031371))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_031380 else g32p_supplierForest_node_031409) else (if i.val < 219 then g32p_supplierForest_node_031420 else g32p_supplierForest_node_031490)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_031529 else g32p_supplierForest_node_031540) else (if i.val < 223 then g32p_supplierForest_node_031564 else g32p_supplierForest_node_031613))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_031620 else g32p_supplierForest_node_031637) else (if i.val < 227 then g32p_supplierForest_node_031641 else g32p_supplierForest_node_031649)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_031653 else g32p_supplierForest_node_031670) else (if i.val < 231 then g32p_supplierForest_node_031672 else g32p_supplierForest_node_031684))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_031712 else g32p_supplierForest_node_031734) else (if i.val < 235 then g32p_supplierForest_node_031739 else g32p_supplierForest_node_031813)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_031853 else g32p_supplierForest_node_031877) else (if i.val < 239 then g32p_supplierForest_node_031898 else g32p_supplierForest_node_031912)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_031925 else g32p_supplierForest_node_031927) else (if i.val < 243 then g32p_supplierForest_node_031929 else g32p_supplierForest_node_031935)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_031942 else g32p_supplierForest_node_031943) else (if i.val < 247 then g32p_supplierForest_node_031947 else g32p_supplierForest_node_031949))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_031952 else g32p_supplierForest_node_031970) else (if i.val < 251 then g32p_supplierForest_node_032015 else g32p_supplierForest_node_032054)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_032067 else g32p_supplierForest_node_032084) else (if i.val < 255 then g32p_supplierForest_node_032103 else g32p_supplierForest_node_032126))))))))

def g32p_supplierForest_classes_036 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 60) else (if i.val < 3 then 15 else 57)) else (if i.val < 6 then (if i.val < 5 then 29 else 15) else (if i.val < 7 then 59 else 16))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 31) else (if i.val < 11 then 63 else 57)) else (if i.val < 14 then (if i.val < 13 then 57 else 57) else (if i.val < 15 then 62 else 60)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 15 else 30) else (if i.val < 19 then 15 else 57)) else (if i.val < 22 then (if i.val < 21 then 30 else 30) else (if i.val < 23 then 16 else 16))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 31 else 31) else (if i.val < 27 then 32 else 14)) else (if i.val < 30 then (if i.val < 29 then 15 else 15) else (if i.val < 31 then 57 else 30))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 14 else 29) else (if i.val < 35 then 33 else 34)) else (if i.val < 38 then (if i.val < 37 then 34 else 16) else (if i.val < 39 then 17 else 14))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 30 else 29) else (if i.val < 43 then 15 else 31)) else (if i.val < 46 then (if i.val < 45 then 3 else 15) else (if i.val < 47 then 34 else 33)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 15 else 14) else (if i.val < 51 then 34 else 15)) else (if i.val < 54 then (if i.val < 53 then 57 else 17) else (if i.val < 55 then 15 else 15))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 17 else 34) else (if i.val < 59 then 14 else 34)) else (if i.val < 62 then (if i.val < 61 then 29 else 15) else (if i.val < 63 then 30 else 30)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 16 else 16) else (if i.val < 67 then 34 else 14)) else (if i.val < 70 then (if i.val < 69 then 3 else 57) else (if i.val < 71 then 58 else 32))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 58 else 16) else (if i.val < 75 then 31 else 57)) else (if i.val < 78 then (if i.val < 77 then 57 else 57) else (if i.val < 79 then 31 else 30)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 57 else 30) else (if i.val < 83 then 4 else 57)) else (if i.val < 86 then (if i.val < 85 then 15 else 57) else (if i.val < 87 then 17 else 34))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 32 else 32) else (if i.val < 91 then 17 else 57)) else (if i.val < 94 then (if i.val < 93 then 66 else 32) else (if i.val < 95 then 57 else 57))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 29 else 4) else (if i.val < 99 then 36 else 16)) else (if i.val < 102 then (if i.val < 101 then 63 else 30) else (if i.val < 103 then 63 else 63))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 16 else 33) else (if i.val < 107 then 16 else 32)) else (if i.val < 110 then (if i.val < 109 then 16 else 32) else (if i.val < 111 then 4 else 30)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 16 else 31) else (if i.val < 115 then 4 else 32)) else (if i.val < 118 then (if i.val < 117 then 16 else 57) else (if i.val < 119 then 57 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 32 else 32) else (if i.val < 123 then 58 else 62)) else (if i.val < 126 then (if i.val < 125 then 32 else 34) else (if i.val < 127 then 32 else 16))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 57 else 15) else (if i.val < 131 then 16 else 57)) else (if i.val < 134 then (if i.val < 133 then 17 else 30) else (if i.val < 135 then 59 else 16))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 57 else 14) else (if i.val < 139 then 30 else 30)) else (if i.val < 142 then (if i.val < 141 then 29 else 57) else (if i.val < 143 then 57 else 29)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 17 else 4) else (if i.val < 147 then 34 else 57)) else (if i.val < 150 then (if i.val < 149 then 15 else 62) else (if i.val < 151 then 29 else 32))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 30 else 31) else (if i.val < 155 then 4 else 58)) else (if i.val < 158 then (if i.val < 157 then 14 else 31) else (if i.val < 159 then 3 else 30))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 30 else 30) else (if i.val < 163 then 32 else 16)) else (if i.val < 166 then (if i.val < 165 then 34 else 59) else (if i.val < 167 then 16 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 57 else 63) else (if i.val < 171 then 36 else 16)) else (if i.val < 174 then (if i.val < 173 then 30 else 63) else (if i.val < 175 then 57 else 57)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 65 else 32) else (if i.val < 179 then 30 else 57)) else (if i.val < 182 then (if i.val < 181 then 15 else 30) else (if i.val < 183 then 57 else 59))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 16) else (if i.val < 187 then 61 else 57)) else (if i.val < 190 then (if i.val < 189 then 36 else 15) else (if i.val < 191 then 30 else 64)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 16 else 59) else (if i.val < 195 then 16 else 15)) else (if i.val < 198 then (if i.val < 197 then 16 else 17) else (if i.val < 199 then 60 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 31 else 17) else (if i.val < 203 then 31 else 36)) else (if i.val < 206 then (if i.val < 205 then 16 else 31) else (if i.val < 207 then 16 else 32)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 32 else 16) else (if i.val < 211 then 57 else 63)) else (if i.val < 214 then (if i.val < 213 then 65 else 15) else (if i.val < 215 then 16 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 30 else 64) else (if i.val < 219 then 34 else 31)) else (if i.val < 222 then (if i.val < 221 then 57 else 15) else (if i.val < 223 then 36 else 63))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 16 else 16) else (if i.val < 227 then 62 else 36)) else (if i.val < 230 then (if i.val < 229 then 17 else 59) else (if i.val < 231 then 57 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 16 else 57) else (if i.val < 235 then 59 else 59)) else (if i.val < 238 then (if i.val < 237 then 64 else 33) else (if i.val < 239 then 16 else 30)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 16) else (if i.val < 243 then 36 else 4)) else (if i.val < 246 then (if i.val < 245 then 32 else 32) else (if i.val < 247 then 30 else 32))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 30 else 63) else (if i.val < 251 then 65 else 57)) else (if i.val < 254 then (if i.val < 253 then 64 else 16) else (if i.val < 255 then 57 else 60))))))))

theorem g32p_supplierForest_actual_036 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_036 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_036 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_026489
  · exact g32p_supplierForest_actual_026560
  · exact g32p_supplierForest_actual_026655
  · exact g32p_supplierForest_actual_026692
  · exact g32p_supplierForest_actual_026735
  · exact g32p_supplierForest_actual_026739
  · exact g32p_supplierForest_actual_026803
  · exact g32p_supplierForest_actual_026837
  · exact g32p_supplierForest_actual_026857
  · exact g32p_supplierForest_actual_026867
  · exact g32p_supplierForest_actual_026872
  · exact g32p_supplierForest_actual_026905
  · exact g32p_supplierForest_actual_026921
  · exact g32p_supplierForest_actual_026968
  · exact g32p_supplierForest_actual_026986
  · exact g32p_supplierForest_actual_026990
  · exact g32p_supplierForest_actual_027046
  · exact g32p_supplierForest_actual_027051
  · exact g32p_supplierForest_actual_027099
  · exact g32p_supplierForest_actual_027106
  · exact g32p_supplierForest_actual_027120
  · exact g32p_supplierForest_actual_027122
  · exact g32p_supplierForest_actual_027336
  · exact g32p_supplierForest_actual_027354
  · exact g32p_supplierForest_actual_027403
  · exact g32p_supplierForest_actual_027430
  · exact g32p_supplierForest_actual_027432
  · exact g32p_supplierForest_actual_027438
  · exact g32p_supplierForest_actual_027482
  · exact g32p_supplierForest_actual_027489
  · exact g32p_supplierForest_actual_027498
  · exact g32p_supplierForest_actual_027521
  · exact g32p_supplierForest_actual_027569
  · exact g32p_supplierForest_actual_027576
  · exact g32p_supplierForest_actual_027659
  · exact g32p_supplierForest_actual_027661
  · exact g32p_supplierForest_actual_027684
  · exact g32p_supplierForest_actual_027689
  · exact g32p_supplierForest_actual_027713
  · exact g32p_supplierForest_actual_027743
  · exact g32p_supplierForest_actual_027755
  · exact g32p_supplierForest_actual_027757
  · exact g32p_supplierForest_actual_027771
  · exact g32p_supplierForest_actual_027782
  · exact g32p_supplierForest_actual_027785
  · exact g32p_supplierForest_actual_027944
  · exact g32p_supplierForest_actual_027986
  · exact g32p_supplierForest_actual_027987
  · exact g32p_supplierForest_actual_028001
  · exact g32p_supplierForest_actual_028015
  · exact g32p_supplierForest_actual_028020
  · exact g32p_supplierForest_actual_028066
  · exact g32p_supplierForest_actual_028108
  · exact g32p_supplierForest_actual_028131
  · exact g32p_supplierForest_actual_028136
  · exact g32p_supplierForest_actual_028176
  · exact g32p_supplierForest_actual_028184
  · exact g32p_supplierForest_actual_028208
  · exact g32p_supplierForest_actual_028228
  · exact g32p_supplierForest_actual_028229
  · exact g32p_supplierForest_actual_028241
  · exact g32p_supplierForest_actual_028275
  · exact g32p_supplierForest_actual_028298
  · exact g32p_supplierForest_actual_028305
  · exact g32p_supplierForest_actual_028308
  · exact g32p_supplierForest_actual_028343
  · exact g32p_supplierForest_actual_028364
  · exact g32p_supplierForest_actual_028376
  · exact g32p_supplierForest_actual_028393
  · exact g32p_supplierForest_actual_028425
  · exact g32p_supplierForest_actual_028429
  · exact g32p_supplierForest_actual_028445
  · exact g32p_supplierForest_actual_028452
  · exact g32p_supplierForest_actual_028463
  · exact g32p_supplierForest_actual_028470
  · exact g32p_supplierForest_actual_028476
  · exact g32p_supplierForest_actual_028483
  · exact g32p_supplierForest_actual_028488
  · exact g32p_supplierForest_actual_028512
  · exact g32p_supplierForest_actual_028513
  · exact g32p_supplierForest_actual_028517
  · exact g32p_supplierForest_actual_028545
  · exact g32p_supplierForest_actual_028560
  · exact g32p_supplierForest_actual_028567
  · exact g32p_supplierForest_actual_028581
  · exact g32p_supplierForest_actual_028582
  · exact g32p_supplierForest_actual_028583
  · exact g32p_supplierForest_actual_028594
  · exact g32p_supplierForest_actual_028642
  · exact g32p_supplierForest_actual_028677
  · exact g32p_supplierForest_actual_028682
  · exact g32p_supplierForest_actual_028694
  · exact g32p_supplierForest_actual_028728
  · exact g32p_supplierForest_actual_028731
  · exact g32p_supplierForest_actual_028737
  · exact g32p_supplierForest_actual_028739
  · exact g32p_supplierForest_actual_028744
  · exact g32p_supplierForest_actual_028758
  · exact g32p_supplierForest_actual_028790
  · exact g32p_supplierForest_actual_028795
  · exact g32p_supplierForest_actual_028815
  · exact g32p_supplierForest_actual_028836
  · exact g32p_supplierForest_actual_028874
  · exact g32p_supplierForest_actual_028876
  · exact g32p_supplierForest_actual_028925
  · exact g32p_supplierForest_actual_028940
  · exact g32p_supplierForest_actual_028971
  · exact g32p_supplierForest_actual_028973
  · exact g32p_supplierForest_actual_029016
  · exact g32p_supplierForest_actual_029058
  · exact g32p_supplierForest_actual_029069
  · exact g32p_supplierForest_actual_029072
  · exact g32p_supplierForest_actual_029075
  · exact g32p_supplierForest_actual_029094
  · exact g32p_supplierForest_actual_029095
  · exact g32p_supplierForest_actual_029138
  · exact g32p_supplierForest_actual_029143
  · exact g32p_supplierForest_actual_029184
  · exact g32p_supplierForest_actual_029207
  · exact g32p_supplierForest_actual_029228
  · exact g32p_supplierForest_actual_029231
  · exact g32p_supplierForest_actual_029232
  · exact g32p_supplierForest_actual_029249
  · exact g32p_supplierForest_actual_029268
  · exact g32p_supplierForest_actual_029333
  · exact g32p_supplierForest_actual_029344
  · exact g32p_supplierForest_actual_029359
  · exact g32p_supplierForest_actual_029366
  · exact g32p_supplierForest_actual_029378
  · exact g32p_supplierForest_actual_029406
  · exact g32p_supplierForest_actual_029415
  · exact g32p_supplierForest_actual_029433
  · exact g32p_supplierForest_actual_029437
  · exact g32p_supplierForest_actual_029448
  · exact g32p_supplierForest_actual_029458
  · exact g32p_supplierForest_actual_029466
  · exact g32p_supplierForest_actual_029499
  · exact g32p_supplierForest_actual_029505
  · exact g32p_supplierForest_actual_029514
  · exact g32p_supplierForest_actual_029526
  · exact g32p_supplierForest_actual_029528
  · exact g32p_supplierForest_actual_029568
  · exact g32p_supplierForest_actual_029569
  · exact g32p_supplierForest_actual_029601
  · exact g32p_supplierForest_actual_029647
  · exact g32p_supplierForest_actual_029719
  · exact g32p_supplierForest_actual_029771
  · exact g32p_supplierForest_actual_029776
  · exact g32p_supplierForest_actual_029777
  · exact g32p_supplierForest_actual_029800
  · exact g32p_supplierForest_actual_029839
  · exact g32p_supplierForest_actual_029862
  · exact g32p_supplierForest_actual_029883
  · exact g32p_supplierForest_actual_029925
  · exact g32p_supplierForest_actual_029928
  · exact g32p_supplierForest_actual_029951
  · exact g32p_supplierForest_actual_029962
  · exact g32p_supplierForest_actual_029986
  · exact g32p_supplierForest_actual_030036
  · exact g32p_supplierForest_actual_030080
  · exact g32p_supplierForest_actual_030087
  · exact g32p_supplierForest_actual_030107
  · exact g32p_supplierForest_actual_030118
  · exact g32p_supplierForest_actual_030122
  · exact g32p_supplierForest_actual_030136
  · exact g32p_supplierForest_actual_030145
  · exact g32p_supplierForest_actual_030175
  · exact g32p_supplierForest_actual_030196
  · exact g32p_supplierForest_actual_030205
  · exact g32p_supplierForest_actual_030211
  · exact g32p_supplierForest_actual_030248
  · exact g32p_supplierForest_actual_030252
  · exact g32p_supplierForest_actual_030254
  · exact g32p_supplierForest_actual_030268
  · exact g32p_supplierForest_actual_030271
  · exact g32p_supplierForest_actual_030283
  · exact g32p_supplierForest_actual_030323
  · exact g32p_supplierForest_actual_030355
  · exact g32p_supplierForest_actual_030415
  · exact g32p_supplierForest_actual_030433
  · exact g32p_supplierForest_actual_030472
  · exact g32p_supplierForest_actual_030487
  · exact g32p_supplierForest_actual_030505
  · exact g32p_supplierForest_actual_030547
  · exact g32p_supplierForest_actual_030578
  · exact g32p_supplierForest_actual_030597
  · exact g32p_supplierForest_actual_030600
  · exact g32p_supplierForest_actual_030608
  · exact g32p_supplierForest_actual_030617
  · exact g32p_supplierForest_actual_030629
  · exact g32p_supplierForest_actual_030650
  · exact g32p_supplierForest_actual_030653
  · exact g32p_supplierForest_actual_030659
  · exact g32p_supplierForest_actual_030686
  · exact g32p_supplierForest_actual_030741
  · exact g32p_supplierForest_actual_030780
  · exact g32p_supplierForest_actual_030781
  · exact g32p_supplierForest_actual_030787
  · exact g32p_supplierForest_actual_030903
  · exact g32p_supplierForest_actual_030918
  · exact g32p_supplierForest_actual_030964
  · exact g32p_supplierForest_actual_031001
  · exact g32p_supplierForest_actual_031003
  · exact g32p_supplierForest_actual_031131
  · exact g32p_supplierForest_actual_031138
  · exact g32p_supplierForest_actual_031150
  · exact g32p_supplierForest_actual_031152
  · exact g32p_supplierForest_actual_031153
  · exact g32p_supplierForest_actual_031226
  · exact g32p_supplierForest_actual_031233
  · exact g32p_supplierForest_actual_031250
  · exact g32p_supplierForest_actual_031266
  · exact g32p_supplierForest_actual_031280
  · exact g32p_supplierForest_actual_031282
  · exact g32p_supplierForest_actual_031358
  · exact g32p_supplierForest_actual_031371
  · exact g32p_supplierForest_actual_031380
  · exact g32p_supplierForest_actual_031409
  · exact g32p_supplierForest_actual_031420
  · exact g32p_supplierForest_actual_031490
  · exact g32p_supplierForest_actual_031529
  · exact g32p_supplierForest_actual_031540
  · exact g32p_supplierForest_actual_031564
  · exact g32p_supplierForest_actual_031613
  · exact g32p_supplierForest_actual_031620
  · exact g32p_supplierForest_actual_031637
  · exact g32p_supplierForest_actual_031641
  · exact g32p_supplierForest_actual_031649
  · exact g32p_supplierForest_actual_031653
  · exact g32p_supplierForest_actual_031670
  · exact g32p_supplierForest_actual_031672
  · exact g32p_supplierForest_actual_031684
  · exact g32p_supplierForest_actual_031712
  · exact g32p_supplierForest_actual_031734
  · exact g32p_supplierForest_actual_031739
  · exact g32p_supplierForest_actual_031813
  · exact g32p_supplierForest_actual_031853
  · exact g32p_supplierForest_actual_031877
  · exact g32p_supplierForest_actual_031898
  · exact g32p_supplierForest_actual_031912
  · exact g32p_supplierForest_actual_031925
  · exact g32p_supplierForest_actual_031927
  · exact g32p_supplierForest_actual_031929
  · exact g32p_supplierForest_actual_031935
  · exact g32p_supplierForest_actual_031942
  · exact g32p_supplierForest_actual_031943
  · exact g32p_supplierForest_actual_031947
  · exact g32p_supplierForest_actual_031949
  · exact g32p_supplierForest_actual_031952
  · exact g32p_supplierForest_actual_031970
  · exact g32p_supplierForest_actual_032015
  · exact g32p_supplierForest_actual_032054
  · exact g32p_supplierForest_actual_032067
  · exact g32p_supplierForest_actual_032084
  · exact g32p_supplierForest_actual_032103
  · exact g32p_supplierForest_actual_032126

def g32p_supplierForest_nodes_037 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_032140 else g32p_supplierForest_node_032143) else (if i.val < 3 then g32p_supplierForest_node_032167 else g32p_supplierForest_node_032187)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_032193 else g32p_supplierForest_node_032201) else (if i.val < 7 then g32p_supplierForest_node_032203 else g32p_supplierForest_node_032205))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_032209 else g32p_supplierForest_node_032270) else (if i.val < 11 then g32p_supplierForest_node_032282 else g32p_supplierForest_node_032300)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_032332 else g32p_supplierForest_node_032374) else (if i.val < 15 then g32p_supplierForest_node_032430 else g32p_supplierForest_node_032440)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_032442 else g32p_supplierForest_node_032452) else (if i.val < 19 then g32p_supplierForest_node_032466 else g32p_supplierForest_node_032479)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_032521 else g32p_supplierForest_node_032523) else (if i.val < 23 then g32p_supplierForest_node_032537 else g32p_supplierForest_node_032582))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_032602 else g32p_supplierForest_node_032632) else (if i.val < 27 then g32p_supplierForest_node_032646 else g32p_supplierForest_node_032651)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_032659 else g32p_supplierForest_node_032685) else (if i.val < 31 then g32p_supplierForest_node_032694 else g32p_supplierForest_node_032713))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_032718 else g32p_supplierForest_node_032722) else (if i.val < 35 then g32p_supplierForest_node_032747 else g32p_supplierForest_node_032779)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_032820 else g32p_supplierForest_node_032825) else (if i.val < 39 then g32p_supplierForest_node_032830 else g32p_supplierForest_node_032840))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_032842 else g32p_supplierForest_node_032854) else (if i.val < 43 then g32p_supplierForest_node_032865 else g32p_supplierForest_node_032881)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_032909 else g32p_supplierForest_node_032960) else (if i.val < 47 then g32p_supplierForest_node_032988 else g32p_supplierForest_node_033080)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_033158 else g32p_supplierForest_node_033159) else (if i.val < 51 then g32p_supplierForest_node_033208 else g32p_supplierForest_node_033243)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_033271 else g32p_supplierForest_node_033304) else (if i.val < 55 then g32p_supplierForest_node_033329 else g32p_supplierForest_node_033337))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_033357 else g32p_supplierForest_node_033388) else (if i.val < 59 then g32p_supplierForest_node_033453 else g32p_supplierForest_node_033458)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_033493 else g32p_supplierForest_node_033514) else (if i.val < 63 then g32p_supplierForest_node_033518 else g32p_supplierForest_node_033582)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_033665 else g32p_supplierForest_node_033709) else (if i.val < 67 then g32p_supplierForest_node_033717 else g32p_supplierForest_node_033778)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_033794 else g32p_supplierForest_node_033799) else (if i.val < 71 then g32p_supplierForest_node_033817 else g32p_supplierForest_node_033932))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_033950 else g32p_supplierForest_node_033958) else (if i.val < 75 then g32p_supplierForest_node_034014 else g32p_supplierForest_node_034020)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_034062 else g32p_supplierForest_node_034098) else (if i.val < 79 then g32p_supplierForest_node_034126 else g32p_supplierForest_node_034161)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_034185 else g32p_supplierForest_node_034208) else (if i.val < 83 then g32p_supplierForest_node_034261 else g32p_supplierForest_node_034281)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_034300 else g32p_supplierForest_node_034314) else (if i.val < 87 then g32p_supplierForest_node_034356 else g32p_supplierForest_node_034357))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_034383 else g32p_supplierForest_node_034415) else (if i.val < 91 then g32p_supplierForest_node_034430 else g32p_supplierForest_node_034480)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_034501 else g32p_supplierForest_node_034543) else (if i.val < 95 then g32p_supplierForest_node_034546 else g32p_supplierForest_node_034567))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_034571 else g32p_supplierForest_node_034585) else (if i.val < 99 then g32p_supplierForest_node_034596 else g32p_supplierForest_node_034601)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_034637 else g32p_supplierForest_node_034715) else (if i.val < 103 then g32p_supplierForest_node_034750 else g32p_supplierForest_node_034762))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_034781 else g32p_supplierForest_node_034788) else (if i.val < 107 then g32p_supplierForest_node_034805 else g32p_supplierForest_node_034806)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_034809 else g32p_supplierForest_node_034821) else (if i.val < 111 then g32p_supplierForest_node_034849 else g32p_supplierForest_node_034921)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_034925 else g32p_supplierForest_node_034928) else (if i.val < 115 then g32p_supplierForest_node_034930 else g32p_supplierForest_node_034942)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_034981 else g32p_supplierForest_node_034984) else (if i.val < 119 then g32p_supplierForest_node_034985 else g32p_supplierForest_node_034996))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_035005 else g32p_supplierForest_node_035007) else (if i.val < 123 then g32p_supplierForest_node_035052 else g32p_supplierForest_node_035093)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_035110 else g32p_supplierForest_node_035111) else (if i.val < 127 then g32p_supplierForest_node_035120 else g32p_supplierForest_node_035154))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_035159 else g32p_supplierForest_node_035162) else (if i.val < 131 then g32p_supplierForest_node_035202 else g32p_supplierForest_node_035210)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_035245 else g32p_supplierForest_node_035273) else (if i.val < 135 then g32p_supplierForest_node_035279 else g32p_supplierForest_node_035309))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_035330 else g32p_supplierForest_node_035335) else (if i.val < 139 then g32p_supplierForest_node_035386 else g32p_supplierForest_node_035391)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_035392 else g32p_supplierForest_node_035401) else (if i.val < 143 then g32p_supplierForest_node_035405 else g32p_supplierForest_node_035406)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_035550 else g32p_supplierForest_node_035568) else (if i.val < 147 then g32p_supplierForest_node_035591 else g32p_supplierForest_node_035598)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_035620 else g32p_supplierForest_node_035692) else (if i.val < 151 then g32p_supplierForest_node_035708 else g32p_supplierForest_node_035732))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_035789 else g32p_supplierForest_node_035794) else (if i.val < 155 then g32p_supplierForest_node_035841 else g32p_supplierForest_node_035842)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_035855 else g32p_supplierForest_node_035892) else (if i.val < 159 then g32p_supplierForest_node_035922 else g32p_supplierForest_node_035934))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_035958 else g32p_supplierForest_node_035977) else (if i.val < 163 then g32p_supplierForest_node_036020 else g32p_supplierForest_node_036056)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_036100 else g32p_supplierForest_node_036121) else (if i.val < 167 then g32p_supplierForest_node_036133 else g32p_supplierForest_node_036136))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_036152 else g32p_supplierForest_node_036176) else (if i.val < 171 then g32p_supplierForest_node_036248 else g32p_supplierForest_node_036323)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_036360 else g32p_supplierForest_node_036371) else (if i.val < 175 then g32p_supplierForest_node_036384 else g32p_supplierForest_node_036406)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_036429 else g32p_supplierForest_node_036442) else (if i.val < 179 then g32p_supplierForest_node_036458 else g32p_supplierForest_node_036488)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_036500 else g32p_supplierForest_node_036503) else (if i.val < 183 then g32p_supplierForest_node_036534 else g32p_supplierForest_node_036574))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_036581 else g32p_supplierForest_node_036631) else (if i.val < 187 then g32p_supplierForest_node_036651 else g32p_supplierForest_node_036652)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_036700 else g32p_supplierForest_node_036710) else (if i.val < 191 then g32p_supplierForest_node_036735 else g32p_supplierForest_node_036774)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_036781 else g32p_supplierForest_node_036788) else (if i.val < 195 then g32p_supplierForest_node_036822 else g32p_supplierForest_node_036878)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_036904 else g32p_supplierForest_node_036912) else (if i.val < 199 then g32p_supplierForest_node_036917 else g32p_supplierForest_node_036978))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_036993 else g32p_supplierForest_node_036994) else (if i.val < 203 then g32p_supplierForest_node_036997 else g32p_supplierForest_node_037007)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_037008 else g32p_supplierForest_node_037023) else (if i.val < 207 then g32p_supplierForest_node_037042 else g32p_supplierForest_node_037046)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_037081 else g32p_supplierForest_node_037150) else (if i.val < 211 then g32p_supplierForest_node_037195 else g32p_supplierForest_node_037211)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_037267 else g32p_supplierForest_node_037269) else (if i.val < 215 then g32p_supplierForest_node_037300 else g32p_supplierForest_node_037348))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_037435 else g32p_supplierForest_node_037441) else (if i.val < 219 then g32p_supplierForest_node_037445 else g32p_supplierForest_node_037448)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_037454 else g32p_supplierForest_node_037486) else (if i.val < 223 then g32p_supplierForest_node_037557 else g32p_supplierForest_node_037604))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_037617 else g32p_supplierForest_node_037619) else (if i.val < 227 then g32p_supplierForest_node_037633 else g32p_supplierForest_node_037654)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_037663 else g32p_supplierForest_node_037669) else (if i.val < 231 then g32p_supplierForest_node_037689 else g32p_supplierForest_node_037695))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_037739 else g32p_supplierForest_node_037790) else (if i.val < 235 then g32p_supplierForest_node_037804 else g32p_supplierForest_node_037809)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_037821 else g32p_supplierForest_node_037827) else (if i.val < 239 then g32p_supplierForest_node_037884 else g32p_supplierForest_node_037939)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_037945 else g32p_supplierForest_node_037976) else (if i.val < 243 then g32p_supplierForest_node_037981 else g32p_supplierForest_node_038007)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_038064 else g32p_supplierForest_node_038070) else (if i.val < 247 then g32p_supplierForest_node_038093 else g32p_supplierForest_node_038105))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_038133 else g32p_supplierForest_node_038157) else (if i.val < 251 then g32p_supplierForest_node_038158 else g32p_supplierForest_node_038166)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_038171 else g32p_supplierForest_node_038198) else (if i.val < 255 then g32p_supplierForest_node_038199 else g32p_supplierForest_node_038200))))))))

def g32p_supplierForest_classes_037 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 59 else 29) else (if i.val < 3 then 57 else 63)) else (if i.val < 6 then (if i.val < 5 then 61 else 57) else (if i.val < 7 then 58 else 59))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 60 else 57) else (if i.val < 11 then 16 else 57)) else (if i.val < 14 then (if i.val < 13 then 63 else 58) else (if i.val < 15 then 34 else 64)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 63 else 16) else (if i.val < 19 then 4 else 65)) else (if i.val < 22 then (if i.val < 21 then 31 else 4) else (if i.val < 23 then 30 else 17))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 59 else 30) else (if i.val < 27 then 60 else 4)) else (if i.val < 30 then (if i.val < 29 then 4 else 32) else (if i.val < 31 then 30 else 59))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 59 else 57) else (if i.val < 35 then 59 else 29)) else (if i.val < 38 then (if i.val < 37 then 16 else 4) else (if i.val < 39 then 30 else 30))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 57 else 64) else (if i.val < 43 then 57 else 57)) else (if i.val < 46 then (if i.val < 45 then 57 else 16) else (if i.val < 47 then 32 else 17)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 17) else (if i.val < 51 then 16 else 30)) else (if i.val < 54 then (if i.val < 53 then 30 else 66) else (if i.val < 55 then 30 else 32))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 59 else 30) else (if i.val < 59 then 63 else 17)) else (if i.val < 62 then (if i.val < 61 then 32 else 14) else (if i.val < 63 then 16 else 61)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 30 else 57) else (if i.val < 67 then 16 else 34)) else (if i.val < 70 then (if i.val < 69 then 64 else 3) else (if i.val < 71 then 34 else 62))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 34 else 32) else (if i.val < 75 then 30 else 16)) else (if i.val < 78 then (if i.val < 77 then 29 else 32) else (if i.val < 79 then 32 else 32)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 16 else 15) else (if i.val < 83 then 32 else 14)) else (if i.val < 86 then (if i.val < 85 then 57 else 57) else (if i.val < 87 then 30 else 33))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 59 else 36) else (if i.val < 91 then 30 else 17)) else (if i.val < 94 then (if i.val < 93 then 57 else 57) else (if i.val < 95 then 30 else 16))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 33 else 17) else (if i.val < 99 then 34 else 15)) else (if i.val < 102 then (if i.val < 101 then 14 else 34) else (if i.val < 103 then 4 else 57))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 36 else 30) else (if i.val < 107 then 16 else 59)) else (if i.val < 110 then (if i.val < 109 then 60 else 15) else (if i.val < 111 then 34 else 61)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 59 else 59) else (if i.val < 115 then 60 else 16)) else (if i.val < 118 then (if i.val < 117 then 57 else 58) else (if i.val < 119 then 15 else 59))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 34 else 59) else (if i.val < 123 then 59 else 16)) else (if i.val < 126 then (if i.val < 125 then 57 else 64) else (if i.val < 127 then 32 else 64))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 30 else 30) else (if i.val < 131 then 57 else 15)) else (if i.val < 134 then (if i.val < 133 then 33 else 32) else (if i.val < 135 then 17 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 57 else 64) else (if i.val < 139 then 14 else 30)) else (if i.val < 142 then (if i.val < 141 then 32 else 30) else (if i.val < 143 then 30 else 29)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 16 else 34) else (if i.val < 147 then 57 else 30)) else (if i.val < 150 then (if i.val < 149 then 57 else 64) else (if i.val < 151 then 16 else 63))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 34 else 58) else (if i.val < 155 then 65 else 14)) else (if i.val < 158 then (if i.val < 157 then 3 else 57) else (if i.val < 159 then 57 else 32))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 63 else 36) else (if i.val < 163 then 30 else 57)) else (if i.val < 166 then (if i.val < 165 then 60 else 57) else (if i.val < 167 then 59 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 31 else 16) else (if i.val < 171 then 66 else 31)) else (if i.val < 174 then (if i.val < 173 then 32 else 16) else (if i.val < 175 then 36 else 57)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 34 else 35) else (if i.val < 179 then 14 else 59)) else (if i.val < 182 then (if i.val < 181 then 34 else 29) else (if i.val < 183 then 57 else 35))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 32 else 15) else (if i.val < 187 then 59 else 15)) else (if i.val < 190 then (if i.val < 189 then 15 else 30) else (if i.val < 191 then 57 else 15)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 15) else (if i.val < 195 then 29 else 34)) else (if i.val < 198 then (if i.val < 197 then 57 else 57) else (if i.val < 199 then 34 else 30))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 32 else 32) else (if i.val < 203 then 59 else 60)) else (if i.val < 206 then (if i.val < 205 then 30 else 15) else (if i.val < 207 then 3 else 15)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 57 else 61) else (if i.val < 211 then 15 else 14)) else (if i.val < 214 then (if i.val < 213 then 63 else 57) else (if i.val < 215 then 30 else 34))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 17 else 16) else (if i.val < 219 then 16 else 16)) else (if i.val < 222 then (if i.val < 221 then 58 else 33) else (if i.val < 223 then 33 else 34))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 15 else 17) else (if i.val < 227 then 16 else 35)) else (if i.val < 230 then (if i.val < 229 then 30 else 16) else (if i.val < 231 then 16 else 30))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 16 else 15) else (if i.val < 235 then 57 else 57)) else (if i.val < 238 then (if i.val < 237 then 15 else 30) else (if i.val < 239 then 16 else 16)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 16 else 29) else (if i.val < 243 then 15 else 14)) else (if i.val < 246 then (if i.val < 245 then 34 else 61) else (if i.val < 247 then 31 else 57))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 15 else 15) else (if i.val < 251 then 14 else 29)) else (if i.val < 254 then (if i.val < 253 then 57 else 32) else (if i.val < 255 then 58 else 59))))))))

theorem g32p_supplierForest_actual_037 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_037 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_037 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_032140
  · exact g32p_supplierForest_actual_032143
  · exact g32p_supplierForest_actual_032167
  · exact g32p_supplierForest_actual_032187
  · exact g32p_supplierForest_actual_032193
  · exact g32p_supplierForest_actual_032201
  · exact g32p_supplierForest_actual_032203
  · exact g32p_supplierForest_actual_032205
  · exact g32p_supplierForest_actual_032209
  · exact g32p_supplierForest_actual_032270
  · exact g32p_supplierForest_actual_032282
  · exact g32p_supplierForest_actual_032300
  · exact g32p_supplierForest_actual_032332
  · exact g32p_supplierForest_actual_032374
  · exact g32p_supplierForest_actual_032430
  · exact g32p_supplierForest_actual_032440
  · exact g32p_supplierForest_actual_032442
  · exact g32p_supplierForest_actual_032452
  · exact g32p_supplierForest_actual_032466
  · exact g32p_supplierForest_actual_032479
  · exact g32p_supplierForest_actual_032521
  · exact g32p_supplierForest_actual_032523
  · exact g32p_supplierForest_actual_032537
  · exact g32p_supplierForest_actual_032582
  · exact g32p_supplierForest_actual_032602
  · exact g32p_supplierForest_actual_032632
  · exact g32p_supplierForest_actual_032646
  · exact g32p_supplierForest_actual_032651
  · exact g32p_supplierForest_actual_032659
  · exact g32p_supplierForest_actual_032685
  · exact g32p_supplierForest_actual_032694
  · exact g32p_supplierForest_actual_032713
  · exact g32p_supplierForest_actual_032718
  · exact g32p_supplierForest_actual_032722
  · exact g32p_supplierForest_actual_032747
  · exact g32p_supplierForest_actual_032779
  · exact g32p_supplierForest_actual_032820
  · exact g32p_supplierForest_actual_032825
  · exact g32p_supplierForest_actual_032830
  · exact g32p_supplierForest_actual_032840
  · exact g32p_supplierForest_actual_032842
  · exact g32p_supplierForest_actual_032854
  · exact g32p_supplierForest_actual_032865
  · exact g32p_supplierForest_actual_032881
  · exact g32p_supplierForest_actual_032909
  · exact g32p_supplierForest_actual_032960
  · exact g32p_supplierForest_actual_032988
  · exact g32p_supplierForest_actual_033080
  · exact g32p_supplierForest_actual_033158
  · exact g32p_supplierForest_actual_033159
  · exact g32p_supplierForest_actual_033208
  · exact g32p_supplierForest_actual_033243
  · exact g32p_supplierForest_actual_033271
  · exact g32p_supplierForest_actual_033304
  · exact g32p_supplierForest_actual_033329
  · exact g32p_supplierForest_actual_033337
  · exact g32p_supplierForest_actual_033357
  · exact g32p_supplierForest_actual_033388
  · exact g32p_supplierForest_actual_033453
  · exact g32p_supplierForest_actual_033458
  · exact g32p_supplierForest_actual_033493
  · exact g32p_supplierForest_actual_033514
  · exact g32p_supplierForest_actual_033518
  · exact g32p_supplierForest_actual_033582
  · exact g32p_supplierForest_actual_033665
  · exact g32p_supplierForest_actual_033709
  · exact g32p_supplierForest_actual_033717
  · exact g32p_supplierForest_actual_033778
  · exact g32p_supplierForest_actual_033794
  · exact g32p_supplierForest_actual_033799
  · exact g32p_supplierForest_actual_033817
  · exact g32p_supplierForest_actual_033932
  · exact g32p_supplierForest_actual_033950
  · exact g32p_supplierForest_actual_033958
  · exact g32p_supplierForest_actual_034014
  · exact g32p_supplierForest_actual_034020
  · exact g32p_supplierForest_actual_034062
  · exact g32p_supplierForest_actual_034098
  · exact g32p_supplierForest_actual_034126
  · exact g32p_supplierForest_actual_034161
  · exact g32p_supplierForest_actual_034185
  · exact g32p_supplierForest_actual_034208
  · exact g32p_supplierForest_actual_034261
  · exact g32p_supplierForest_actual_034281
  · exact g32p_supplierForest_actual_034300
  · exact g32p_supplierForest_actual_034314
  · exact g32p_supplierForest_actual_034356
  · exact g32p_supplierForest_actual_034357
  · exact g32p_supplierForest_actual_034383
  · exact g32p_supplierForest_actual_034415
  · exact g32p_supplierForest_actual_034430
  · exact g32p_supplierForest_actual_034480
  · exact g32p_supplierForest_actual_034501
  · exact g32p_supplierForest_actual_034543
  · exact g32p_supplierForest_actual_034546
  · exact g32p_supplierForest_actual_034567
  · exact g32p_supplierForest_actual_034571
  · exact g32p_supplierForest_actual_034585
  · exact g32p_supplierForest_actual_034596
  · exact g32p_supplierForest_actual_034601
  · exact g32p_supplierForest_actual_034637
  · exact g32p_supplierForest_actual_034715
  · exact g32p_supplierForest_actual_034750
  · exact g32p_supplierForest_actual_034762
  · exact g32p_supplierForest_actual_034781
  · exact g32p_supplierForest_actual_034788
  · exact g32p_supplierForest_actual_034805
  · exact g32p_supplierForest_actual_034806
  · exact g32p_supplierForest_actual_034809
  · exact g32p_supplierForest_actual_034821
  · exact g32p_supplierForest_actual_034849
  · exact g32p_supplierForest_actual_034921
  · exact g32p_supplierForest_actual_034925
  · exact g32p_supplierForest_actual_034928
  · exact g32p_supplierForest_actual_034930
  · exact g32p_supplierForest_actual_034942
  · exact g32p_supplierForest_actual_034981
  · exact g32p_supplierForest_actual_034984
  · exact g32p_supplierForest_actual_034985
  · exact g32p_supplierForest_actual_034996
  · exact g32p_supplierForest_actual_035005
  · exact g32p_supplierForest_actual_035007
  · exact g32p_supplierForest_actual_035052
  · exact g32p_supplierForest_actual_035093
  · exact g32p_supplierForest_actual_035110
  · exact g32p_supplierForest_actual_035111
  · exact g32p_supplierForest_actual_035120
  · exact g32p_supplierForest_actual_035154
  · exact g32p_supplierForest_actual_035159
  · exact g32p_supplierForest_actual_035162
  · exact g32p_supplierForest_actual_035202
  · exact g32p_supplierForest_actual_035210
  · exact g32p_supplierForest_actual_035245
  · exact g32p_supplierForest_actual_035273
  · exact g32p_supplierForest_actual_035279
  · exact g32p_supplierForest_actual_035309
  · exact g32p_supplierForest_actual_035330
  · exact g32p_supplierForest_actual_035335
  · exact g32p_supplierForest_actual_035386
  · exact g32p_supplierForest_actual_035391
  · exact g32p_supplierForest_actual_035392
  · exact g32p_supplierForest_actual_035401
  · exact g32p_supplierForest_actual_035405
  · exact g32p_supplierForest_actual_035406
  · exact g32p_supplierForest_actual_035550
  · exact g32p_supplierForest_actual_035568
  · exact g32p_supplierForest_actual_035591
  · exact g32p_supplierForest_actual_035598
  · exact g32p_supplierForest_actual_035620
  · exact g32p_supplierForest_actual_035692
  · exact g32p_supplierForest_actual_035708
  · exact g32p_supplierForest_actual_035732
  · exact g32p_supplierForest_actual_035789
  · exact g32p_supplierForest_actual_035794
  · exact g32p_supplierForest_actual_035841
  · exact g32p_supplierForest_actual_035842
  · exact g32p_supplierForest_actual_035855
  · exact g32p_supplierForest_actual_035892
  · exact g32p_supplierForest_actual_035922
  · exact g32p_supplierForest_actual_035934
  · exact g32p_supplierForest_actual_035958
  · exact g32p_supplierForest_actual_035977
  · exact g32p_supplierForest_actual_036020
  · exact g32p_supplierForest_actual_036056
  · exact g32p_supplierForest_actual_036100
  · exact g32p_supplierForest_actual_036121
  · exact g32p_supplierForest_actual_036133
  · exact g32p_supplierForest_actual_036136
  · exact g32p_supplierForest_actual_036152
  · exact g32p_supplierForest_actual_036176
  · exact g32p_supplierForest_actual_036248
  · exact g32p_supplierForest_actual_036323
  · exact g32p_supplierForest_actual_036360
  · exact g32p_supplierForest_actual_036371
  · exact g32p_supplierForest_actual_036384
  · exact g32p_supplierForest_actual_036406
  · exact g32p_supplierForest_actual_036429
  · exact g32p_supplierForest_actual_036442
  · exact g32p_supplierForest_actual_036458
  · exact g32p_supplierForest_actual_036488
  · exact g32p_supplierForest_actual_036500
  · exact g32p_supplierForest_actual_036503
  · exact g32p_supplierForest_actual_036534
  · exact g32p_supplierForest_actual_036574
  · exact g32p_supplierForest_actual_036581
  · exact g32p_supplierForest_actual_036631
  · exact g32p_supplierForest_actual_036651
  · exact g32p_supplierForest_actual_036652
  · exact g32p_supplierForest_actual_036700
  · exact g32p_supplierForest_actual_036710
  · exact g32p_supplierForest_actual_036735
  · exact g32p_supplierForest_actual_036774
  · exact g32p_supplierForest_actual_036781
  · exact g32p_supplierForest_actual_036788
  · exact g32p_supplierForest_actual_036822
  · exact g32p_supplierForest_actual_036878
  · exact g32p_supplierForest_actual_036904
  · exact g32p_supplierForest_actual_036912
  · exact g32p_supplierForest_actual_036917
  · exact g32p_supplierForest_actual_036978
  · exact g32p_supplierForest_actual_036993
  · exact g32p_supplierForest_actual_036994
  · exact g32p_supplierForest_actual_036997
  · exact g32p_supplierForest_actual_037007
  · exact g32p_supplierForest_actual_037008
  · exact g32p_supplierForest_actual_037023
  · exact g32p_supplierForest_actual_037042
  · exact g32p_supplierForest_actual_037046
  · exact g32p_supplierForest_actual_037081
  · exact g32p_supplierForest_actual_037150
  · exact g32p_supplierForest_actual_037195
  · exact g32p_supplierForest_actual_037211
  · exact g32p_supplierForest_actual_037267
  · exact g32p_supplierForest_actual_037269
  · exact g32p_supplierForest_actual_037300
  · exact g32p_supplierForest_actual_037348
  · exact g32p_supplierForest_actual_037435
  · exact g32p_supplierForest_actual_037441
  · exact g32p_supplierForest_actual_037445
  · exact g32p_supplierForest_actual_037448
  · exact g32p_supplierForest_actual_037454
  · exact g32p_supplierForest_actual_037486
  · exact g32p_supplierForest_actual_037557
  · exact g32p_supplierForest_actual_037604
  · exact g32p_supplierForest_actual_037617
  · exact g32p_supplierForest_actual_037619
  · exact g32p_supplierForest_actual_037633
  · exact g32p_supplierForest_actual_037654
  · exact g32p_supplierForest_actual_037663
  · exact g32p_supplierForest_actual_037669
  · exact g32p_supplierForest_actual_037689
  · exact g32p_supplierForest_actual_037695
  · exact g32p_supplierForest_actual_037739
  · exact g32p_supplierForest_actual_037790
  · exact g32p_supplierForest_actual_037804
  · exact g32p_supplierForest_actual_037809
  · exact g32p_supplierForest_actual_037821
  · exact g32p_supplierForest_actual_037827
  · exact g32p_supplierForest_actual_037884
  · exact g32p_supplierForest_actual_037939
  · exact g32p_supplierForest_actual_037945
  · exact g32p_supplierForest_actual_037976
  · exact g32p_supplierForest_actual_037981
  · exact g32p_supplierForest_actual_038007
  · exact g32p_supplierForest_actual_038064
  · exact g32p_supplierForest_actual_038070
  · exact g32p_supplierForest_actual_038093
  · exact g32p_supplierForest_actual_038105
  · exact g32p_supplierForest_actual_038133
  · exact g32p_supplierForest_actual_038157
  · exact g32p_supplierForest_actual_038158
  · exact g32p_supplierForest_actual_038166
  · exact g32p_supplierForest_actual_038171
  · exact g32p_supplierForest_actual_038198
  · exact g32p_supplierForest_actual_038199
  · exact g32p_supplierForest_actual_038200

def g32p_supplierForest_nodes_038 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_038201 else g32p_supplierForest_node_038206) else (if i.val < 3 then g32p_supplierForest_node_038214 else g32p_supplierForest_node_038224)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_038226 else g32p_supplierForest_node_038241) else (if i.val < 7 then g32p_supplierForest_node_038258 else g32p_supplierForest_node_038262))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_038267 else g32p_supplierForest_node_038293) else (if i.val < 11 then g32p_supplierForest_node_038299 else g32p_supplierForest_node_038303)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_038307 else g32p_supplierForest_node_038317) else (if i.val < 15 then g32p_supplierForest_node_038347 else g32p_supplierForest_node_038380)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_038412 else g32p_supplierForest_node_038452) else (if i.val < 19 then g32p_supplierForest_node_038453 else g32p_supplierForest_node_038455)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_038468 else g32p_supplierForest_node_038534) else (if i.val < 23 then g32p_supplierForest_node_038538 else g32p_supplierForest_node_038543))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_038544 else g32p_supplierForest_node_038588) else (if i.val < 27 then g32p_supplierForest_node_038614 else g32p_supplierForest_node_038617)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_038621 else g32p_supplierForest_node_038624) else (if i.val < 31 then g32p_supplierForest_node_038652 else g32p_supplierForest_node_038655))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_038664 else g32p_supplierForest_node_038680) else (if i.val < 35 then g32p_supplierForest_node_038687 else g32p_supplierForest_node_038716)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_038731 else g32p_supplierForest_node_038736) else (if i.val < 39 then g32p_supplierForest_node_038782 else g32p_supplierForest_node_038824))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_038830 else g32p_supplierForest_node_038840) else (if i.val < 43 then g32p_supplierForest_node_038841 else g32p_supplierForest_node_038861)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_038895 else g32p_supplierForest_node_038926) else (if i.val < 47 then g32p_supplierForest_node_038959 else g32p_supplierForest_node_038968)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_038972 else g32p_supplierForest_node_038987) else (if i.val < 51 then g32p_supplierForest_node_038991 else g32p_supplierForest_node_039045)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_039075 else g32p_supplierForest_node_039114) else (if i.val < 55 then g32p_supplierForest_node_039141 else g32p_supplierForest_node_039147))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_039190 else g32p_supplierForest_node_039207) else (if i.val < 59 then g32p_supplierForest_node_039222 else g32p_supplierForest_node_039241)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_039243 else g32p_supplierForest_node_039260) else (if i.val < 63 then g32p_supplierForest_node_039271 else g32p_supplierForest_node_039343)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_039381 else g32p_supplierForest_node_039418) else (if i.val < 67 then g32p_supplierForest_node_039453 else g32p_supplierForest_node_039457)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_039467 else g32p_supplierForest_node_039481) else (if i.val < 71 then g32p_supplierForest_node_039484 else g32p_supplierForest_node_039552))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_039601 else g32p_supplierForest_node_039609) else (if i.val < 75 then g32p_supplierForest_node_039614 else g32p_supplierForest_node_039736)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_039745 else g32p_supplierForest_node_039759) else (if i.val < 79 then g32p_supplierForest_node_039800 else g32p_supplierForest_node_039819)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_039826 else g32p_supplierForest_node_039880) else (if i.val < 83 then g32p_supplierForest_node_039925 else g32p_supplierForest_node_039933)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_039944 else g32p_supplierForest_node_039987) else (if i.val < 87 then g32p_supplierForest_node_039989 else g32p_supplierForest_node_039994))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_040017 else g32p_supplierForest_node_040051) else (if i.val < 91 then g32p_supplierForest_node_040107 else g32p_supplierForest_node_040145)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_040156 else g32p_supplierForest_node_040174) else (if i.val < 95 then g32p_supplierForest_node_040182 else g32p_supplierForest_node_040185))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_040193 else g32p_supplierForest_node_040220) else (if i.val < 99 then g32p_supplierForest_node_040238 else g32p_supplierForest_node_040250)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_040270 else g32p_supplierForest_node_040277) else (if i.val < 103 then g32p_supplierForest_node_040305 else g32p_supplierForest_node_040363))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_040376 else g32p_supplierForest_node_040385) else (if i.val < 107 then g32p_supplierForest_node_040391 else g32p_supplierForest_node_040401)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_040402 else g32p_supplierForest_node_040417) else (if i.val < 111 then g32p_supplierForest_node_040429 else g32p_supplierForest_node_040437)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_040471 else g32p_supplierForest_node_040485) else (if i.val < 115 then g32p_supplierForest_node_040533 else g32p_supplierForest_node_040619)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_040667 else g32p_supplierForest_node_040681) else (if i.val < 119 then g32p_supplierForest_node_040695 else g32p_supplierForest_node_040744))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_040750 else g32p_supplierForest_node_040883) else (if i.val < 123 then g32p_supplierForest_node_040970 else g32p_supplierForest_node_040973)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_040975 else g32p_supplierForest_node_041000) else (if i.val < 127 then g32p_supplierForest_node_041026 else g32p_supplierForest_node_041046))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_041072 else g32p_supplierForest_node_041180) else (if i.val < 131 then g32p_supplierForest_node_041215 else g32p_supplierForest_node_041226)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_041346 else g32p_supplierForest_node_041373) else (if i.val < 135 then g32p_supplierForest_node_041385 else g32p_supplierForest_node_041393))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_041400 else g32p_supplierForest_node_041403) else (if i.val < 139 then g32p_supplierForest_node_041408 else g32p_supplierForest_node_041410)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_041419 else g32p_supplierForest_node_041420) else (if i.val < 143 then g32p_supplierForest_node_041449 else g32p_supplierForest_node_041460)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_041499 else g32p_supplierForest_node_041500) else (if i.val < 147 then g32p_supplierForest_node_041514 else g32p_supplierForest_node_041517)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_041550 else g32p_supplierForest_node_041576) else (if i.val < 151 then g32p_supplierForest_node_041580 else g32p_supplierForest_node_041590))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_041597 else g32p_supplierForest_node_041599) else (if i.val < 155 then g32p_supplierForest_node_041605 else g32p_supplierForest_node_041691)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_041737 else g32p_supplierForest_node_041807) else (if i.val < 159 then g32p_supplierForest_node_041838 else g32p_supplierForest_node_041853))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_041859 else g32p_supplierForest_node_041904) else (if i.val < 163 then g32p_supplierForest_node_041947 else g32p_supplierForest_node_041948)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_041989 else g32p_supplierForest_node_041991) else (if i.val < 167 then g32p_supplierForest_node_042005 else g32p_supplierForest_node_042008))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_042016 else g32p_supplierForest_node_042075) else (if i.val < 171 then g32p_supplierForest_node_042102 else g32p_supplierForest_node_042106)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_042165 else g32p_supplierForest_node_042167) else (if i.val < 175 then g32p_supplierForest_node_042185 else g32p_supplierForest_node_042244)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_042250 else g32p_supplierForest_node_042406) else (if i.val < 179 then g32p_supplierForest_node_042451 else g32p_supplierForest_node_042506)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_042524 else g32p_supplierForest_node_042551) else (if i.val < 183 then g32p_supplierForest_node_042553 else g32p_supplierForest_node_042567))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_042575 else g32p_supplierForest_node_042583) else (if i.val < 187 then g32p_supplierForest_node_042593 else g32p_supplierForest_node_042613)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_042624 else g32p_supplierForest_node_042661) else (if i.val < 191 then g32p_supplierForest_node_042719 else g32p_supplierForest_node_042774)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_042801 else g32p_supplierForest_node_042840) else (if i.val < 195 then g32p_supplierForest_node_042849 else g32p_supplierForest_node_042850)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_042852 else g32p_supplierForest_node_042903) else (if i.val < 199 then g32p_supplierForest_node_042913 else g32p_supplierForest_node_042932))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_042977 else g32p_supplierForest_node_043004) else (if i.val < 203 then g32p_supplierForest_node_043090 else g32p_supplierForest_node_043104)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_043121 else g32p_supplierForest_node_043149) else (if i.val < 207 then g32p_supplierForest_node_043166 else g32p_supplierForest_node_043235)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_043241 else g32p_supplierForest_node_043264) else (if i.val < 211 then g32p_supplierForest_node_043293 else g32p_supplierForest_node_043317)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_043341 else g32p_supplierForest_node_043406) else (if i.val < 215 then g32p_supplierForest_node_043456 else g32p_supplierForest_node_043480))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_043483 else g32p_supplierForest_node_043511) else (if i.val < 219 then g32p_supplierForest_node_043594 else g32p_supplierForest_node_043618)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_043644 else g32p_supplierForest_node_043683) else (if i.val < 223 then g32p_supplierForest_node_043773 else g32p_supplierForest_node_043788))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_043804 else g32p_supplierForest_node_043807) else (if i.val < 227 then g32p_supplierForest_node_043809 else g32p_supplierForest_node_043850)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_043855 else g32p_supplierForest_node_043872) else (if i.val < 231 then g32p_supplierForest_node_043873 else g32p_supplierForest_node_043904))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_043964 else g32p_supplierForest_node_043974) else (if i.val < 235 then g32p_supplierForest_node_044023 else g32p_supplierForest_node_044066)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_044067 else g32p_supplierForest_node_044080) else (if i.val < 239 then g32p_supplierForest_node_044087 else g32p_supplierForest_node_044094)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_044123 else g32p_supplierForest_node_044164) else (if i.val < 243 then g32p_supplierForest_node_044167 else g32p_supplierForest_node_044177)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_044200 else g32p_supplierForest_node_044212) else (if i.val < 247 then g32p_supplierForest_node_044221 else g32p_supplierForest_node_044234))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_044240 else g32p_supplierForest_node_044242) else (if i.val < 251 then g32p_supplierForest_node_044296 else g32p_supplierForest_node_044298)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_044301 else g32p_supplierForest_node_044303) else (if i.val < 255 then g32p_supplierForest_node_044352 else g32p_supplierForest_node_044440))))))))

def g32p_supplierForest_classes_038 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 30) else (if i.val < 3 then 16 else 34)) else (if i.val < 6 then (if i.val < 5 then 30 else 30) else (if i.val < 7 then 34 else 29))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 29 else 30) else (if i.val < 11 then 32 else 57)) else (if i.val < 14 then (if i.val < 13 then 16 else 32) else (if i.val < 15 then 36 else 62)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 34 else 34) else (if i.val < 19 then 33 else 58)) else (if i.val < 22 then (if i.val < 21 then 34 else 16) else (if i.val < 23 then 16 else 4))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 16 else 58) else (if i.val < 27 then 30 else 36)) else (if i.val < 30 then (if i.val < 29 then 34 else 16) else (if i.val < 31 then 4 else 4))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 32) else (if i.val < 35 then 16 else 34)) else (if i.val < 38 then (if i.val < 37 then 15 else 32) else (if i.val < 39 then 57 else 35))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 60 else 15) else (if i.val < 43 then 34 else 17)) else (if i.val < 46 then (if i.val < 45 then 58 else 61) else (if i.val < 47 then 34 else 29)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 57 else 14) else (if i.val < 51 then 34 else 16)) else (if i.val < 54 then (if i.val < 53 then 34 else 30) else (if i.val < 55 then 16 else 63))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 61 else 30) else (if i.val < 59 then 30 else 64)) else (if i.val < 62 then (if i.val < 61 then 4 else 30) else (if i.val < 63 then 14 else 32)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 16 else 30) else (if i.val < 67 then 35 else 59)) else (if i.val < 70 then (if i.val < 69 then 35 else 58) else (if i.val < 71 then 57 else 15))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 32 else 4) else (if i.val < 75 then 58 else 30)) else (if i.val < 78 then (if i.val < 77 then 32 else 30) else (if i.val < 79 then 32 else 65)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 57 else 63) else (if i.val < 83 then 57 else 63)) else (if i.val < 86 then (if i.val < 85 then 58 else 62) else (if i.val < 87 then 63 else 59))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 29 else 29) else (if i.val < 91 then 36 else 29)) else (if i.val < 94 then (if i.val < 93 then 29 else 30) else (if i.val < 95 then 29 else 15))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 32) else (if i.val < 99 then 32 else 34)) else (if i.val < 102 then (if i.val < 101 then 57 else 57) else (if i.val < 103 then 30 else 34))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 30 else 30) else (if i.val < 107 then 57 else 30)) else (if i.val < 110 then (if i.val < 109 then 62 else 57) else (if i.val < 111 then 60 else 57)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 15 else 36) else (if i.val < 115 then 30 else 65)) else (if i.val < 118 then (if i.val < 117 then 15 else 61) else (if i.val < 119 then 16 else 63))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 60 else 34) else (if i.val < 123 then 64 else 58)) else (if i.val < 126 then (if i.val < 125 then 63 else 34) else (if i.val < 127 then 57 else 61))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 63 else 63) else (if i.val < 131 then 30 else 34)) else (if i.val < 134 then (if i.val < 133 then 34 else 29) else (if i.val < 135 then 59 else 58))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 16 else 30) else (if i.val < 139 then 14 else 36)) else (if i.val < 142 then (if i.val < 141 then 58 else 30) else (if i.val < 143 then 30 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 58 else 17) else (if i.val < 147 then 30 else 35)) else (if i.val < 150 then (if i.val < 149 then 14 else 57) else (if i.val < 151 then 29 else 16))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 14 else 15) else (if i.val < 155 then 60 else 60)) else (if i.val < 158 then (if i.val < 157 then 15 else 34) else (if i.val < 159 then 14 else 17))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 15 else 34) else (if i.val < 163 then 15 else 3)) else (if i.val < 166 then (if i.val < 165 then 34 else 32) else (if i.val < 167 then 29 else 34))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 36 else 34) else (if i.val < 171 then 17 else 34)) else (if i.val < 174 then (if i.val < 173 then 16 else 14) else (if i.val < 175 then 30 else 16)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 62 else 32) else (if i.val < 179 then 36 else 63)) else (if i.val < 182 then (if i.val < 181 then 64 else 30) else (if i.val < 183 then 16 else 4))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 34 else 59) else (if i.val < 187 then 57 else 34)) else (if i.val < 190 then (if i.val < 189 then 32 else 57) else (if i.val < 191 then 58 else 15)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 14 else 17) else (if i.val < 195 then 60 else 16)) else (if i.val < 198 then (if i.val < 197 then 34 else 29) else (if i.val < 199 then 34 else 34))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 62 else 36) else (if i.val < 203 then 57 else 15)) else (if i.val < 206 then (if i.val < 205 then 63 else 58) else (if i.val < 207 then 57 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 33 else 34) else (if i.val < 211 then 35 else 34)) else (if i.val < 214 then (if i.val < 213 then 30 else 63) else (if i.val < 215 then 34 else 15))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 65 else 16) else (if i.val < 219 then 30 else 63)) else (if i.val < 222 then (if i.val < 221 then 36 else 34) else (if i.val < 223 then 30 else 36))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 58) else (if i.val < 227 then 58 else 15)) else (if i.val < 230 then (if i.val < 229 then 29 else 35) else (if i.val < 231 then 59 else 35))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 34 else 34) else (if i.val < 235 then 30 else 35)) else (if i.val < 238 then (if i.val < 237 then 33 else 16) else (if i.val < 239 then 15 else 15)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 59) else (if i.val < 243 then 30 else 60)) else (if i.val < 246 then (if i.val < 245 then 36 else 33) else (if i.val < 247 then 57 else 33))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 16 else 31) else (if i.val < 251 then 32 else 57)) else (if i.val < 254 then (if i.val < 253 then 58 else 34) else (if i.val < 255 then 17 else 21))))))))

theorem g32p_supplierForest_actual_038 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_038 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_038 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_038201
  · exact g32p_supplierForest_actual_038206
  · exact g32p_supplierForest_actual_038214
  · exact g32p_supplierForest_actual_038224
  · exact g32p_supplierForest_actual_038226
  · exact g32p_supplierForest_actual_038241
  · exact g32p_supplierForest_actual_038258
  · exact g32p_supplierForest_actual_038262
  · exact g32p_supplierForest_actual_038267
  · exact g32p_supplierForest_actual_038293
  · exact g32p_supplierForest_actual_038299
  · exact g32p_supplierForest_actual_038303
  · exact g32p_supplierForest_actual_038307
  · exact g32p_supplierForest_actual_038317
  · exact g32p_supplierForest_actual_038347
  · exact g32p_supplierForest_actual_038380
  · exact g32p_supplierForest_actual_038412
  · exact g32p_supplierForest_actual_038452
  · exact g32p_supplierForest_actual_038453
  · exact g32p_supplierForest_actual_038455
  · exact g32p_supplierForest_actual_038468
  · exact g32p_supplierForest_actual_038534
  · exact g32p_supplierForest_actual_038538
  · exact g32p_supplierForest_actual_038543
  · exact g32p_supplierForest_actual_038544
  · exact g32p_supplierForest_actual_038588
  · exact g32p_supplierForest_actual_038614
  · exact g32p_supplierForest_actual_038617
  · exact g32p_supplierForest_actual_038621
  · exact g32p_supplierForest_actual_038624
  · exact g32p_supplierForest_actual_038652
  · exact g32p_supplierForest_actual_038655
  · exact g32p_supplierForest_actual_038664
  · exact g32p_supplierForest_actual_038680
  · exact g32p_supplierForest_actual_038687
  · exact g32p_supplierForest_actual_038716
  · exact g32p_supplierForest_actual_038731
  · exact g32p_supplierForest_actual_038736
  · exact g32p_supplierForest_actual_038782
  · exact g32p_supplierForest_actual_038824
  · exact g32p_supplierForest_actual_038830
  · exact g32p_supplierForest_actual_038840
  · exact g32p_supplierForest_actual_038841
  · exact g32p_supplierForest_actual_038861
  · exact g32p_supplierForest_actual_038895
  · exact g32p_supplierForest_actual_038926
  · exact g32p_supplierForest_actual_038959
  · exact g32p_supplierForest_actual_038968
  · exact g32p_supplierForest_actual_038972
  · exact g32p_supplierForest_actual_038987
  · exact g32p_supplierForest_actual_038991
  · exact g32p_supplierForest_actual_039045
  · exact g32p_supplierForest_actual_039075
  · exact g32p_supplierForest_actual_039114
  · exact g32p_supplierForest_actual_039141
  · exact g32p_supplierForest_actual_039147
  · exact g32p_supplierForest_actual_039190
  · exact g32p_supplierForest_actual_039207
  · exact g32p_supplierForest_actual_039222
  · exact g32p_supplierForest_actual_039241
  · exact g32p_supplierForest_actual_039243
  · exact g32p_supplierForest_actual_039260
  · exact g32p_supplierForest_actual_039271
  · exact g32p_supplierForest_actual_039343
  · exact g32p_supplierForest_actual_039381
  · exact g32p_supplierForest_actual_039418
  · exact g32p_supplierForest_actual_039453
  · exact g32p_supplierForest_actual_039457
  · exact g32p_supplierForest_actual_039467
  · exact g32p_supplierForest_actual_039481
  · exact g32p_supplierForest_actual_039484
  · exact g32p_supplierForest_actual_039552
  · exact g32p_supplierForest_actual_039601
  · exact g32p_supplierForest_actual_039609
  · exact g32p_supplierForest_actual_039614
  · exact g32p_supplierForest_actual_039736
  · exact g32p_supplierForest_actual_039745
  · exact g32p_supplierForest_actual_039759
  · exact g32p_supplierForest_actual_039800
  · exact g32p_supplierForest_actual_039819
  · exact g32p_supplierForest_actual_039826
  · exact g32p_supplierForest_actual_039880
  · exact g32p_supplierForest_actual_039925
  · exact g32p_supplierForest_actual_039933
  · exact g32p_supplierForest_actual_039944
  · exact g32p_supplierForest_actual_039987
  · exact g32p_supplierForest_actual_039989
  · exact g32p_supplierForest_actual_039994
  · exact g32p_supplierForest_actual_040017
  · exact g32p_supplierForest_actual_040051
  · exact g32p_supplierForest_actual_040107
  · exact g32p_supplierForest_actual_040145
  · exact g32p_supplierForest_actual_040156
  · exact g32p_supplierForest_actual_040174
  · exact g32p_supplierForest_actual_040182
  · exact g32p_supplierForest_actual_040185
  · exact g32p_supplierForest_actual_040193
  · exact g32p_supplierForest_actual_040220
  · exact g32p_supplierForest_actual_040238
  · exact g32p_supplierForest_actual_040250
  · exact g32p_supplierForest_actual_040270
  · exact g32p_supplierForest_actual_040277
  · exact g32p_supplierForest_actual_040305
  · exact g32p_supplierForest_actual_040363
  · exact g32p_supplierForest_actual_040376
  · exact g32p_supplierForest_actual_040385
  · exact g32p_supplierForest_actual_040391
  · exact g32p_supplierForest_actual_040401
  · exact g32p_supplierForest_actual_040402
  · exact g32p_supplierForest_actual_040417
  · exact g32p_supplierForest_actual_040429
  · exact g32p_supplierForest_actual_040437
  · exact g32p_supplierForest_actual_040471
  · exact g32p_supplierForest_actual_040485
  · exact g32p_supplierForest_actual_040533
  · exact g32p_supplierForest_actual_040619
  · exact g32p_supplierForest_actual_040667
  · exact g32p_supplierForest_actual_040681
  · exact g32p_supplierForest_actual_040695
  · exact g32p_supplierForest_actual_040744
  · exact g32p_supplierForest_actual_040750
  · exact g32p_supplierForest_actual_040883
  · exact g32p_supplierForest_actual_040970
  · exact g32p_supplierForest_actual_040973
  · exact g32p_supplierForest_actual_040975
  · exact g32p_supplierForest_actual_041000
  · exact g32p_supplierForest_actual_041026
  · exact g32p_supplierForest_actual_041046
  · exact g32p_supplierForest_actual_041072
  · exact g32p_supplierForest_actual_041180
  · exact g32p_supplierForest_actual_041215
  · exact g32p_supplierForest_actual_041226
  · exact g32p_supplierForest_actual_041346
  · exact g32p_supplierForest_actual_041373
  · exact g32p_supplierForest_actual_041385
  · exact g32p_supplierForest_actual_041393
  · exact g32p_supplierForest_actual_041400
  · exact g32p_supplierForest_actual_041403
  · exact g32p_supplierForest_actual_041408
  · exact g32p_supplierForest_actual_041410
  · exact g32p_supplierForest_actual_041419
  · exact g32p_supplierForest_actual_041420
  · exact g32p_supplierForest_actual_041449
  · exact g32p_supplierForest_actual_041460
  · exact g32p_supplierForest_actual_041499
  · exact g32p_supplierForest_actual_041500
  · exact g32p_supplierForest_actual_041514
  · exact g32p_supplierForest_actual_041517
  · exact g32p_supplierForest_actual_041550
  · exact g32p_supplierForest_actual_041576
  · exact g32p_supplierForest_actual_041580
  · exact g32p_supplierForest_actual_041590
  · exact g32p_supplierForest_actual_041597
  · exact g32p_supplierForest_actual_041599
  · exact g32p_supplierForest_actual_041605
  · exact g32p_supplierForest_actual_041691
  · exact g32p_supplierForest_actual_041737
  · exact g32p_supplierForest_actual_041807
  · exact g32p_supplierForest_actual_041838
  · exact g32p_supplierForest_actual_041853
  · exact g32p_supplierForest_actual_041859
  · exact g32p_supplierForest_actual_041904
  · exact g32p_supplierForest_actual_041947
  · exact g32p_supplierForest_actual_041948
  · exact g32p_supplierForest_actual_041989
  · exact g32p_supplierForest_actual_041991
  · exact g32p_supplierForest_actual_042005
  · exact g32p_supplierForest_actual_042008
  · exact g32p_supplierForest_actual_042016
  · exact g32p_supplierForest_actual_042075
  · exact g32p_supplierForest_actual_042102
  · exact g32p_supplierForest_actual_042106
  · exact g32p_supplierForest_actual_042165
  · exact g32p_supplierForest_actual_042167
  · exact g32p_supplierForest_actual_042185
  · exact g32p_supplierForest_actual_042244
  · exact g32p_supplierForest_actual_042250
  · exact g32p_supplierForest_actual_042406
  · exact g32p_supplierForest_actual_042451
  · exact g32p_supplierForest_actual_042506
  · exact g32p_supplierForest_actual_042524
  · exact g32p_supplierForest_actual_042551
  · exact g32p_supplierForest_actual_042553
  · exact g32p_supplierForest_actual_042567
  · exact g32p_supplierForest_actual_042575
  · exact g32p_supplierForest_actual_042583
  · exact g32p_supplierForest_actual_042593
  · exact g32p_supplierForest_actual_042613
  · exact g32p_supplierForest_actual_042624
  · exact g32p_supplierForest_actual_042661
  · exact g32p_supplierForest_actual_042719
  · exact g32p_supplierForest_actual_042774
  · exact g32p_supplierForest_actual_042801
  · exact g32p_supplierForest_actual_042840
  · exact g32p_supplierForest_actual_042849
  · exact g32p_supplierForest_actual_042850
  · exact g32p_supplierForest_actual_042852
  · exact g32p_supplierForest_actual_042903
  · exact g32p_supplierForest_actual_042913
  · exact g32p_supplierForest_actual_042932
  · exact g32p_supplierForest_actual_042977
  · exact g32p_supplierForest_actual_043004
  · exact g32p_supplierForest_actual_043090
  · exact g32p_supplierForest_actual_043104
  · exact g32p_supplierForest_actual_043121
  · exact g32p_supplierForest_actual_043149
  · exact g32p_supplierForest_actual_043166
  · exact g32p_supplierForest_actual_043235
  · exact g32p_supplierForest_actual_043241
  · exact g32p_supplierForest_actual_043264
  · exact g32p_supplierForest_actual_043293
  · exact g32p_supplierForest_actual_043317
  · exact g32p_supplierForest_actual_043341
  · exact g32p_supplierForest_actual_043406
  · exact g32p_supplierForest_actual_043456
  · exact g32p_supplierForest_actual_043480
  · exact g32p_supplierForest_actual_043483
  · exact g32p_supplierForest_actual_043511
  · exact g32p_supplierForest_actual_043594
  · exact g32p_supplierForest_actual_043618
  · exact g32p_supplierForest_actual_043644
  · exact g32p_supplierForest_actual_043683
  · exact g32p_supplierForest_actual_043773
  · exact g32p_supplierForest_actual_043788
  · exact g32p_supplierForest_actual_043804
  · exact g32p_supplierForest_actual_043807
  · exact g32p_supplierForest_actual_043809
  · exact g32p_supplierForest_actual_043850
  · exact g32p_supplierForest_actual_043855
  · exact g32p_supplierForest_actual_043872
  · exact g32p_supplierForest_actual_043873
  · exact g32p_supplierForest_actual_043904
  · exact g32p_supplierForest_actual_043964
  · exact g32p_supplierForest_actual_043974
  · exact g32p_supplierForest_actual_044023
  · exact g32p_supplierForest_actual_044066
  · exact g32p_supplierForest_actual_044067
  · exact g32p_supplierForest_actual_044080
  · exact g32p_supplierForest_actual_044087
  · exact g32p_supplierForest_actual_044094
  · exact g32p_supplierForest_actual_044123
  · exact g32p_supplierForest_actual_044164
  · exact g32p_supplierForest_actual_044167
  · exact g32p_supplierForest_actual_044177
  · exact g32p_supplierForest_actual_044200
  · exact g32p_supplierForest_actual_044212
  · exact g32p_supplierForest_actual_044221
  · exact g32p_supplierForest_actual_044234
  · exact g32p_supplierForest_actual_044240
  · exact g32p_supplierForest_actual_044242
  · exact g32p_supplierForest_actual_044296
  · exact g32p_supplierForest_actual_044298
  · exact g32p_supplierForest_actual_044301
  · exact g32p_supplierForest_actual_044303
  · exact g32p_supplierForest_actual_044352
  · exact g32p_supplierForest_actual_044440

def g32p_supplierForest_nodes_039 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_044491 else g32p_supplierForest_node_044494) else (if i.val < 3 then g32p_supplierForest_node_044496 else g32p_supplierForest_node_044552)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_044578 else g32p_supplierForest_node_044579) else (if i.val < 7 then g32p_supplierForest_node_044582 else g32p_supplierForest_node_044586))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_044697 else g32p_supplierForest_node_044726) else (if i.val < 11 then g32p_supplierForest_node_044729 else g32p_supplierForest_node_044835)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_044838 else g32p_supplierForest_node_044881) else (if i.val < 15 then g32p_supplierForest_node_044899 else g32p_supplierForest_node_044961)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_044977 else g32p_supplierForest_node_044982) else (if i.val < 19 then g32p_supplierForest_node_044985 else g32p_supplierForest_node_045008)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_045044 else g32p_supplierForest_node_045075) else (if i.val < 23 then g32p_supplierForest_node_045079 else g32p_supplierForest_node_045085))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_045094 else g32p_supplierForest_node_045095) else (if i.val < 27 then g32p_supplierForest_node_045111 else g32p_supplierForest_node_045158)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_045180 else g32p_supplierForest_node_045186) else (if i.val < 31 then g32p_supplierForest_node_045199 else g32p_supplierForest_node_045211))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_045217 else g32p_supplierForest_node_045238) else (if i.val < 35 then g32p_supplierForest_node_045242 else g32p_supplierForest_node_045256)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_045261 else g32p_supplierForest_node_045262) else (if i.val < 39 then g32p_supplierForest_node_045297 else g32p_supplierForest_node_045311))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_045347 else g32p_supplierForest_node_045350) else (if i.val < 43 then g32p_supplierForest_node_045357 else g32p_supplierForest_node_045375)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_045438 else g32p_supplierForest_node_045467) else (if i.val < 47 then g32p_supplierForest_node_045472 else g32p_supplierForest_node_045508)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_045557 else g32p_supplierForest_node_045570) else (if i.val < 51 then g32p_supplierForest_node_045601 else g32p_supplierForest_node_045605)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_045632 else g32p_supplierForest_node_045732) else (if i.val < 55 then g32p_supplierForest_node_045768 else g32p_supplierForest_node_045793))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_045824 else g32p_supplierForest_node_045830) else (if i.val < 59 then g32p_supplierForest_node_045851 else g32p_supplierForest_node_045857)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_045872 else g32p_supplierForest_node_045909) else (if i.val < 63 then g32p_supplierForest_node_045913 else g32p_supplierForest_node_045916)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_045919 else g32p_supplierForest_node_045941) else (if i.val < 67 then g32p_supplierForest_node_045968 else g32p_supplierForest_node_045981)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_046010 else g32p_supplierForest_node_046014) else (if i.val < 71 then g32p_supplierForest_node_046024 else g32p_supplierForest_node_046065))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_046073 else g32p_supplierForest_node_046077) else (if i.val < 75 then g32p_supplierForest_node_046078 else g32p_supplierForest_node_046083)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_046092 else g32p_supplierForest_node_046162) else (if i.val < 79 then g32p_supplierForest_node_046166 else g32p_supplierForest_node_046175)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_046201 else g32p_supplierForest_node_046223) else (if i.val < 83 then g32p_supplierForest_node_046241 else g32p_supplierForest_node_046245)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_046249 else g32p_supplierForest_node_046267) else (if i.val < 87 then g32p_supplierForest_node_046272 else g32p_supplierForest_node_046281))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_046291 else g32p_supplierForest_node_046312) else (if i.val < 91 then g32p_supplierForest_node_046366 else g32p_supplierForest_node_046382)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_046386 else g32p_supplierForest_node_046407) else (if i.val < 95 then g32p_supplierForest_node_046427 else g32p_supplierForest_node_046485))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_046511 else g32p_supplierForest_node_046546) else (if i.val < 99 then g32p_supplierForest_node_046582 else g32p_supplierForest_node_046664)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_046677 else g32p_supplierForest_node_046709) else (if i.val < 103 then g32p_supplierForest_node_046772 else g32p_supplierForest_node_046787))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_046801 else g32p_supplierForest_node_046845) else (if i.val < 107 then g32p_supplierForest_node_046849 else g32p_supplierForest_node_046867)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_046882 else g32p_supplierForest_node_046891) else (if i.val < 111 then g32p_supplierForest_node_047016 else g32p_supplierForest_node_047021)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_047049 else g32p_supplierForest_node_047060) else (if i.val < 115 then g32p_supplierForest_node_047076 else g32p_supplierForest_node_047077)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_047095 else g32p_supplierForest_node_047110) else (if i.val < 119 then g32p_supplierForest_node_047120 else g32p_supplierForest_node_047130))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_047159 else g32p_supplierForest_node_047160) else (if i.val < 123 then g32p_supplierForest_node_047166 else g32p_supplierForest_node_047186)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_047253 else g32p_supplierForest_node_047264) else (if i.val < 127 then g32p_supplierForest_node_047269 else g32p_supplierForest_node_047326))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_047332 else g32p_supplierForest_node_047412) else (if i.val < 131 then g32p_supplierForest_node_047435 else g32p_supplierForest_node_047466)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_047475 else g32p_supplierForest_node_047507) else (if i.val < 135 then g32p_supplierForest_node_047521 else g32p_supplierForest_node_047535))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_047546 else g32p_supplierForest_node_047563) else (if i.val < 139 then g32p_supplierForest_node_047565 else g32p_supplierForest_node_047655)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_047704 else g32p_supplierForest_node_047721) else (if i.val < 143 then g32p_supplierForest_node_047724 else g32p_supplierForest_node_047742)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_047746 else g32p_supplierForest_node_047769) else (if i.val < 147 then g32p_supplierForest_node_047837 else g32p_supplierForest_node_047860)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_047867 else g32p_supplierForest_node_047907) else (if i.val < 151 then g32p_supplierForest_node_047925 else g32p_supplierForest_node_047929))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_047942 else g32p_supplierForest_node_047973) else (if i.val < 155 then g32p_supplierForest_node_048097 else g32p_supplierForest_node_048192)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_048249 else g32p_supplierForest_node_048309) else (if i.val < 159 then g32p_supplierForest_node_048326 else g32p_supplierForest_node_048365))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_048378 else g32p_supplierForest_node_048387) else (if i.val < 163 then g32p_supplierForest_node_048439 else g32p_supplierForest_node_048479)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_048501 else g32p_supplierForest_node_048516) else (if i.val < 167 then g32p_supplierForest_node_048518 else g32p_supplierForest_node_048523))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_048525 else g32p_supplierForest_node_048540) else (if i.val < 171 then g32p_supplierForest_node_048567 else g32p_supplierForest_node_048568)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_048588 else g32p_supplierForest_node_048608) else (if i.val < 175 then g32p_supplierForest_node_048675 else g32p_supplierForest_node_048708)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_048721 else g32p_supplierForest_node_048738) else (if i.val < 179 then g32p_supplierForest_node_048762 else g32p_supplierForest_node_048783)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_048795 else g32p_supplierForest_node_048867) else (if i.val < 183 then g32p_supplierForest_node_048868 else g32p_supplierForest_node_048883))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_048903 else g32p_supplierForest_node_049032) else (if i.val < 187 then g32p_supplierForest_node_049102 else g32p_supplierForest_node_049111)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_049122 else g32p_supplierForest_node_049128) else (if i.val < 191 then g32p_supplierForest_node_049168 else g32p_supplierForest_node_049199)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_049225 else g32p_supplierForest_node_049250) else (if i.val < 195 then g32p_supplierForest_node_049271 else g32p_supplierForest_node_049277)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_049284 else g32p_supplierForest_node_049312) else (if i.val < 199 then g32p_supplierForest_node_049383 else g32p_supplierForest_node_049473))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_049564 else g32p_supplierForest_node_049630) else (if i.val < 203 then g32p_supplierForest_node_049644 else g32p_supplierForest_node_049648)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_049716 else g32p_supplierForest_node_049734) else (if i.val < 207 then g32p_supplierForest_node_049761 else g32p_supplierForest_node_049821)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_049853 else g32p_supplierForest_node_049882) else (if i.val < 211 then g32p_supplierForest_node_049921 else g32p_supplierForest_node_049946)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_049962 else g32p_supplierForest_node_049980) else (if i.val < 215 then g32p_supplierForest_node_050012 else g32p_supplierForest_node_050050))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_050051 else g32p_supplierForest_node_050053) else (if i.val < 219 then g32p_supplierForest_node_050119 else g32p_supplierForest_node_050140)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_050168 else g32p_supplierForest_node_050175) else (if i.val < 223 then g32p_supplierForest_node_050177 else g32p_supplierForest_node_050210))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_050233 else g32p_supplierForest_node_050303) else (if i.val < 227 then g32p_supplierForest_node_050304 else g32p_supplierForest_node_050356)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_050361 else g32p_supplierForest_node_050385) else (if i.val < 231 then g32p_supplierForest_node_050387 else g32p_supplierForest_node_050405))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_050413 else g32p_supplierForest_node_050435) else (if i.val < 235 then g32p_supplierForest_node_050450 else g32p_supplierForest_node_050522)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_050548 else g32p_supplierForest_node_050572) else (if i.val < 239 then g32p_supplierForest_node_050614 else g32p_supplierForest_node_050645)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_050708 else g32p_supplierForest_node_050732) else (if i.val < 243 then g32p_supplierForest_node_050785 else g32p_supplierForest_node_050790)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_050916 else g32p_supplierForest_node_050921) else (if i.val < 247 then g32p_supplierForest_node_050956 else g32p_supplierForest_node_050972))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_050974 else g32p_supplierForest_node_051012) else (if i.val < 251 then g32p_supplierForest_node_051024 else g32p_supplierForest_node_051035)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_051048 else g32p_supplierForest_node_051053) else (if i.val < 255 then g32p_supplierForest_node_051055 else g32p_supplierForest_node_051060))))))))

def g32p_supplierForest_classes_039 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 21 else 6) else (if i.val < 3 then 43 else 20)) else (if i.val < 6 then (if i.val < 5 then 22 else 40) else (if i.val < 7 then 39 else 22))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 22) else (if i.val < 11 then 7 else 40)) else (if i.val < 14 then (if i.val < 13 then 41 else 5) else (if i.val < 15 then 24 else 38)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 21 else 40) else (if i.val < 19 then 38 else 44)) else (if i.val < 22 then (if i.val < 21 then 38 else 23) else (if i.val < 23 then 40 else 41))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 39 else 6) else (if i.val < 27 then 39 else 38)) else (if i.val < 30 then (if i.val < 29 then 40 else 38) else (if i.val < 31 then 43 else 40))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 38) else (if i.val < 35 then 20 else 39)) else (if i.val < 38 then (if i.val < 37 then 38 else 21) else (if i.val < 39 then 68 else 22))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 7) else (if i.val < 43 then 69 else 74)) else (if i.val < 46 then (if i.val < 45 then 22 else 38) else (if i.val < 47 then 22 else 7)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 70 else 70) else (if i.val < 51 then 22 else 21)) else (if i.val < 54 then (if i.val < 53 then 23 else 39) else (if i.val < 55 then 38 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 40 else 24) else (if i.val < 59 then 23 else 22)) else (if i.val < 62 then (if i.val < 61 then 19 else 40) else (if i.val < 63 then 74 else 38)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 19 else 72) else (if i.val < 67 then 24 else 71)) else (if i.val < 70 then (if i.val < 69 then 39 else 38) else (if i.val < 71 then 68 else 21))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 42 else 69) else (if i.val < 75 then 38 else 38)) else (if i.val < 78 then (if i.val < 77 then 6 else 21) else (if i.val < 79 then 6 else 38)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 40) else (if i.val < 83 then 6 else 6)) else (if i.val < 86 then (if i.val < 85 then 24 else 38) else (if i.val < 87 then 21 else 38))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 7 else 21) else (if i.val < 91 then 21 else 21)) else (if i.val < 94 then (if i.val < 93 then 70 else 6) else (if i.val < 95 then 22 else 67))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 69 else 38) else (if i.val < 99 then 23 else 23)) else (if i.val < 102 then (if i.val < 101 then 22 else 73) else (if i.val < 103 then 38 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 70 else 41) else (if i.val < 107 then 21 else 6)) else (if i.val < 110 then (if i.val < 109 then 38 else 42) else (if i.val < 111 then 71 else 21)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 70 else 24) else (if i.val < 115 then 22 else 6)) else (if i.val < 118 then (if i.val < 117 then 22 else 38) else (if i.val < 119 then 39 else 21))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 43 else 73) else (if i.val < 123 then 22 else 7)) else (if i.val < 126 then (if i.val < 125 then 21 else 22) else (if i.val < 127 then 69 else 39))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 7 else 6) else (if i.val < 131 then 22 else 6)) else (if i.val < 134 then (if i.val < 133 then 21 else 21) else (if i.val < 135 then 73 else 38))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 6 else 20) else (if i.val < 139 then 71 else 38)) else (if i.val < 142 then (if i.val < 141 then 40 else 74) else (if i.val < 143 then 39 else 7)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 69 else 40) else (if i.val < 147 then 7 else 71)) else (if i.val < 150 then (if i.val < 149 then 69 else 73) else (if i.val < 151 then 74 else 71))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 6 else 7) else (if i.val < 155 then 40 else 40)) else (if i.val < 158 then (if i.val < 157 then 38 else 7) else (if i.val < 159 then 38 else 6))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 74 else 22) else (if i.val < 163 then 7 else 22)) else (if i.val < 166 then (if i.val < 165 then 22 else 74) else (if i.val < 167 then 21 else 73))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 69 else 7) else (if i.val < 171 then 70 else 75)) else (if i.val < 174 then (if i.val < 173 then 69 else 21) else (if i.val < 175 then 40 else 74)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 75 else 73) else (if i.val < 179 then 70 else 38)) else (if i.val < 182 then (if i.val < 181 then 69 else 22) else (if i.val < 183 then 38 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 71 else 21) else (if i.val < 187 then 21 else 38)) else (if i.val < 190 then (if i.val < 189 then 7 else 40) else (if i.val < 191 then 21 else 41)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 41 else 69) else (if i.val < 195 then 5 else 24)) else (if i.val < 198 then (if i.val < 197 then 20 else 24) else (if i.val < 199 then 21 else 40))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 38 else 75) else (if i.val < 203 then 38 else 19)) else (if i.val < 206 then (if i.val < 205 then 23 else 70) else (if i.val < 207 then 22 else 74)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 21 else 6) else (if i.val < 211 then 38 else 43)) else (if i.val < 214 then (if i.val < 213 then 41 else 7) else (if i.val < 215 then 22 else 20))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 70 else 40) else (if i.val < 219 then 69 else 20)) else (if i.val < 222 then (if i.val < 221 then 69 else 38) else (if i.val < 223 then 39 else 40))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 38 else 40) else (if i.val < 227 then 44 else 22)) else (if i.val < 230 then (if i.val < 229 then 40 else 6) else (if i.val < 231 then 39 else 39))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 40 else 38) else (if i.val < 235 then 42 else 20)) else (if i.val < 238 then (if i.val < 237 then 21 else 43) else (if i.val < 239 then 69 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 22 else 39) else (if i.val < 243 then 38 else 23)) else (if i.val < 246 then (if i.val < 245 then 22 else 21) else (if i.val < 247 then 41 else 21))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 40 else 38) else (if i.val < 251 then 21 else 39)) else (if i.val < 254 then (if i.val < 253 then 38 else 39) else (if i.val < 255 then 38 else 7))))))))

theorem g32p_supplierForest_actual_039 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_039 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_039 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_044491
  · exact g32p_supplierForest_actual_044494
  · exact g32p_supplierForest_actual_044496
  · exact g32p_supplierForest_actual_044552
  · exact g32p_supplierForest_actual_044578
  · exact g32p_supplierForest_actual_044579
  · exact g32p_supplierForest_actual_044582
  · exact g32p_supplierForest_actual_044586
  · exact g32p_supplierForest_actual_044697
  · exact g32p_supplierForest_actual_044726
  · exact g32p_supplierForest_actual_044729
  · exact g32p_supplierForest_actual_044835
  · exact g32p_supplierForest_actual_044838
  · exact g32p_supplierForest_actual_044881
  · exact g32p_supplierForest_actual_044899
  · exact g32p_supplierForest_actual_044961
  · exact g32p_supplierForest_actual_044977
  · exact g32p_supplierForest_actual_044982
  · exact g32p_supplierForest_actual_044985
  · exact g32p_supplierForest_actual_045008
  · exact g32p_supplierForest_actual_045044
  · exact g32p_supplierForest_actual_045075
  · exact g32p_supplierForest_actual_045079
  · exact g32p_supplierForest_actual_045085
  · exact g32p_supplierForest_actual_045094
  · exact g32p_supplierForest_actual_045095
  · exact g32p_supplierForest_actual_045111
  · exact g32p_supplierForest_actual_045158
  · exact g32p_supplierForest_actual_045180
  · exact g32p_supplierForest_actual_045186
  · exact g32p_supplierForest_actual_045199
  · exact g32p_supplierForest_actual_045211
  · exact g32p_supplierForest_actual_045217
  · exact g32p_supplierForest_actual_045238
  · exact g32p_supplierForest_actual_045242
  · exact g32p_supplierForest_actual_045256
  · exact g32p_supplierForest_actual_045261
  · exact g32p_supplierForest_actual_045262
  · exact g32p_supplierForest_actual_045297
  · exact g32p_supplierForest_actual_045311
  · exact g32p_supplierForest_actual_045347
  · exact g32p_supplierForest_actual_045350
  · exact g32p_supplierForest_actual_045357
  · exact g32p_supplierForest_actual_045375
  · exact g32p_supplierForest_actual_045438
  · exact g32p_supplierForest_actual_045467
  · exact g32p_supplierForest_actual_045472
  · exact g32p_supplierForest_actual_045508
  · exact g32p_supplierForest_actual_045557
  · exact g32p_supplierForest_actual_045570
  · exact g32p_supplierForest_actual_045601
  · exact g32p_supplierForest_actual_045605
  · exact g32p_supplierForest_actual_045632
  · exact g32p_supplierForest_actual_045732
  · exact g32p_supplierForest_actual_045768
  · exact g32p_supplierForest_actual_045793
  · exact g32p_supplierForest_actual_045824
  · exact g32p_supplierForest_actual_045830
  · exact g32p_supplierForest_actual_045851
  · exact g32p_supplierForest_actual_045857
  · exact g32p_supplierForest_actual_045872
  · exact g32p_supplierForest_actual_045909
  · exact g32p_supplierForest_actual_045913
  · exact g32p_supplierForest_actual_045916
  · exact g32p_supplierForest_actual_045919
  · exact g32p_supplierForest_actual_045941
  · exact g32p_supplierForest_actual_045968
  · exact g32p_supplierForest_actual_045981
  · exact g32p_supplierForest_actual_046010
  · exact g32p_supplierForest_actual_046014
  · exact g32p_supplierForest_actual_046024
  · exact g32p_supplierForest_actual_046065
  · exact g32p_supplierForest_actual_046073
  · exact g32p_supplierForest_actual_046077
  · exact g32p_supplierForest_actual_046078
  · exact g32p_supplierForest_actual_046083
  · exact g32p_supplierForest_actual_046092
  · exact g32p_supplierForest_actual_046162
  · exact g32p_supplierForest_actual_046166
  · exact g32p_supplierForest_actual_046175
  · exact g32p_supplierForest_actual_046201
  · exact g32p_supplierForest_actual_046223
  · exact g32p_supplierForest_actual_046241
  · exact g32p_supplierForest_actual_046245
  · exact g32p_supplierForest_actual_046249
  · exact g32p_supplierForest_actual_046267
  · exact g32p_supplierForest_actual_046272
  · exact g32p_supplierForest_actual_046281
  · exact g32p_supplierForest_actual_046291
  · exact g32p_supplierForest_actual_046312
  · exact g32p_supplierForest_actual_046366
  · exact g32p_supplierForest_actual_046382
  · exact g32p_supplierForest_actual_046386
  · exact g32p_supplierForest_actual_046407
  · exact g32p_supplierForest_actual_046427
  · exact g32p_supplierForest_actual_046485
  · exact g32p_supplierForest_actual_046511
  · exact g32p_supplierForest_actual_046546
  · exact g32p_supplierForest_actual_046582
  · exact g32p_supplierForest_actual_046664
  · exact g32p_supplierForest_actual_046677
  · exact g32p_supplierForest_actual_046709
  · exact g32p_supplierForest_actual_046772
  · exact g32p_supplierForest_actual_046787
  · exact g32p_supplierForest_actual_046801
  · exact g32p_supplierForest_actual_046845
  · exact g32p_supplierForest_actual_046849
  · exact g32p_supplierForest_actual_046867
  · exact g32p_supplierForest_actual_046882
  · exact g32p_supplierForest_actual_046891
  · exact g32p_supplierForest_actual_047016
  · exact g32p_supplierForest_actual_047021
  · exact g32p_supplierForest_actual_047049
  · exact g32p_supplierForest_actual_047060
  · exact g32p_supplierForest_actual_047076
  · exact g32p_supplierForest_actual_047077
  · exact g32p_supplierForest_actual_047095
  · exact g32p_supplierForest_actual_047110
  · exact g32p_supplierForest_actual_047120
  · exact g32p_supplierForest_actual_047130
  · exact g32p_supplierForest_actual_047159
  · exact g32p_supplierForest_actual_047160
  · exact g32p_supplierForest_actual_047166
  · exact g32p_supplierForest_actual_047186
  · exact g32p_supplierForest_actual_047253
  · exact g32p_supplierForest_actual_047264
  · exact g32p_supplierForest_actual_047269
  · exact g32p_supplierForest_actual_047326
  · exact g32p_supplierForest_actual_047332
  · exact g32p_supplierForest_actual_047412
  · exact g32p_supplierForest_actual_047435
  · exact g32p_supplierForest_actual_047466
  · exact g32p_supplierForest_actual_047475
  · exact g32p_supplierForest_actual_047507
  · exact g32p_supplierForest_actual_047521
  · exact g32p_supplierForest_actual_047535
  · exact g32p_supplierForest_actual_047546
  · exact g32p_supplierForest_actual_047563
  · exact g32p_supplierForest_actual_047565
  · exact g32p_supplierForest_actual_047655
  · exact g32p_supplierForest_actual_047704
  · exact g32p_supplierForest_actual_047721
  · exact g32p_supplierForest_actual_047724
  · exact g32p_supplierForest_actual_047742
  · exact g32p_supplierForest_actual_047746
  · exact g32p_supplierForest_actual_047769
  · exact g32p_supplierForest_actual_047837
  · exact g32p_supplierForest_actual_047860
  · exact g32p_supplierForest_actual_047867
  · exact g32p_supplierForest_actual_047907
  · exact g32p_supplierForest_actual_047925
  · exact g32p_supplierForest_actual_047929
  · exact g32p_supplierForest_actual_047942
  · exact g32p_supplierForest_actual_047973
  · exact g32p_supplierForest_actual_048097
  · exact g32p_supplierForest_actual_048192
  · exact g32p_supplierForest_actual_048249
  · exact g32p_supplierForest_actual_048309
  · exact g32p_supplierForest_actual_048326
  · exact g32p_supplierForest_actual_048365
  · exact g32p_supplierForest_actual_048378
  · exact g32p_supplierForest_actual_048387
  · exact g32p_supplierForest_actual_048439
  · exact g32p_supplierForest_actual_048479
  · exact g32p_supplierForest_actual_048501
  · exact g32p_supplierForest_actual_048516
  · exact g32p_supplierForest_actual_048518
  · exact g32p_supplierForest_actual_048523
  · exact g32p_supplierForest_actual_048525
  · exact g32p_supplierForest_actual_048540
  · exact g32p_supplierForest_actual_048567
  · exact g32p_supplierForest_actual_048568
  · exact g32p_supplierForest_actual_048588
  · exact g32p_supplierForest_actual_048608
  · exact g32p_supplierForest_actual_048675
  · exact g32p_supplierForest_actual_048708
  · exact g32p_supplierForest_actual_048721
  · exact g32p_supplierForest_actual_048738
  · exact g32p_supplierForest_actual_048762
  · exact g32p_supplierForest_actual_048783
  · exact g32p_supplierForest_actual_048795
  · exact g32p_supplierForest_actual_048867
  · exact g32p_supplierForest_actual_048868
  · exact g32p_supplierForest_actual_048883
  · exact g32p_supplierForest_actual_048903
  · exact g32p_supplierForest_actual_049032
  · exact g32p_supplierForest_actual_049102
  · exact g32p_supplierForest_actual_049111
  · exact g32p_supplierForest_actual_049122
  · exact g32p_supplierForest_actual_049128
  · exact g32p_supplierForest_actual_049168
  · exact g32p_supplierForest_actual_049199
  · exact g32p_supplierForest_actual_049225
  · exact g32p_supplierForest_actual_049250
  · exact g32p_supplierForest_actual_049271
  · exact g32p_supplierForest_actual_049277
  · exact g32p_supplierForest_actual_049284
  · exact g32p_supplierForest_actual_049312
  · exact g32p_supplierForest_actual_049383
  · exact g32p_supplierForest_actual_049473
  · exact g32p_supplierForest_actual_049564
  · exact g32p_supplierForest_actual_049630
  · exact g32p_supplierForest_actual_049644
  · exact g32p_supplierForest_actual_049648
  · exact g32p_supplierForest_actual_049716
  · exact g32p_supplierForest_actual_049734
  · exact g32p_supplierForest_actual_049761
  · exact g32p_supplierForest_actual_049821
  · exact g32p_supplierForest_actual_049853
  · exact g32p_supplierForest_actual_049882
  · exact g32p_supplierForest_actual_049921
  · exact g32p_supplierForest_actual_049946
  · exact g32p_supplierForest_actual_049962
  · exact g32p_supplierForest_actual_049980
  · exact g32p_supplierForest_actual_050012
  · exact g32p_supplierForest_actual_050050
  · exact g32p_supplierForest_actual_050051
  · exact g32p_supplierForest_actual_050053
  · exact g32p_supplierForest_actual_050119
  · exact g32p_supplierForest_actual_050140
  · exact g32p_supplierForest_actual_050168
  · exact g32p_supplierForest_actual_050175
  · exact g32p_supplierForest_actual_050177
  · exact g32p_supplierForest_actual_050210
  · exact g32p_supplierForest_actual_050233
  · exact g32p_supplierForest_actual_050303
  · exact g32p_supplierForest_actual_050304
  · exact g32p_supplierForest_actual_050356
  · exact g32p_supplierForest_actual_050361
  · exact g32p_supplierForest_actual_050385
  · exact g32p_supplierForest_actual_050387
  · exact g32p_supplierForest_actual_050405
  · exact g32p_supplierForest_actual_050413
  · exact g32p_supplierForest_actual_050435
  · exact g32p_supplierForest_actual_050450
  · exact g32p_supplierForest_actual_050522
  · exact g32p_supplierForest_actual_050548
  · exact g32p_supplierForest_actual_050572
  · exact g32p_supplierForest_actual_050614
  · exact g32p_supplierForest_actual_050645
  · exact g32p_supplierForest_actual_050708
  · exact g32p_supplierForest_actual_050732
  · exact g32p_supplierForest_actual_050785
  · exact g32p_supplierForest_actual_050790
  · exact g32p_supplierForest_actual_050916
  · exact g32p_supplierForest_actual_050921
  · exact g32p_supplierForest_actual_050956
  · exact g32p_supplierForest_actual_050972
  · exact g32p_supplierForest_actual_050974
  · exact g32p_supplierForest_actual_051012
  · exact g32p_supplierForest_actual_051024
  · exact g32p_supplierForest_actual_051035
  · exact g32p_supplierForest_actual_051048
  · exact g32p_supplierForest_actual_051053
  · exact g32p_supplierForest_actual_051055
  · exact g32p_supplierForest_actual_051060

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_051070 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_051070 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051070 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064418 := by
  decide +kernel

theorem g32p_supplierForest_actual_051070 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051070) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_051070
    g32p_supplierForest_actual_064418

def g32p_supplierForest_node_051084 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_051084 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051084 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_060812 := by
  decide +kernel

theorem g32p_supplierForest_actual_051084 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051084) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 0 g32p_supplierForest_edge_051084
    g32p_supplierForest_actual_060812

def g32p_supplierForest_node_051092 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051092 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051092 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_059160 := by
  decide +kernel

theorem g32p_supplierForest_actual_051092 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051092) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_051092
    g32p_supplierForest_actual_059160

def g32p_supplierForest_node_051115 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_051115 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051115 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_045294 := by
  decide +kernel

theorem g32p_supplierForest_actual_051115 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051115) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_051115
    g32p_supplierForest_actual_045294

def g32p_supplierForest_node_051128 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_051128 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051128 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_051337 := by
  decide +kernel

theorem g32p_supplierForest_actual_051128 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051128) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_051128
    g32p_supplierForest_actual_051337

def g32p_supplierForest_node_051140 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_051140 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051140 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009733 := by
  decide +kernel

theorem g32p_supplierForest_actual_051140 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051140) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 0 g32p_supplierForest_edge_051140
    g32p_supplierForest_actual_009733

def g32p_supplierForest_node_051169 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_051169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051169 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012275 := by
  decide +kernel

theorem g32p_supplierForest_actual_051169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051169) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_051169
    g32p_supplierForest_actual_012275

def g32p_supplierForest_node_051174 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_051174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051174 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_045475 := by
  decide +kernel

theorem g32p_supplierForest_actual_051174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051174) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 1 g32p_supplierForest_edge_051174
    g32p_supplierForest_actual_045475

def g32p_supplierForest_node_051244 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_051244 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051244 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051818 := by
  decide +kernel

theorem g32p_supplierForest_actual_051244 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051244) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_051244
    g32p_supplierForest_actual_051818

def g32p_supplierForest_node_051292 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_051292 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051292 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047962 := by
  decide +kernel

theorem g32p_supplierForest_actual_051292 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051292) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_051292
    g32p_supplierForest_actual_047962

def g32p_supplierForest_node_051360 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_051360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051360 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051869 := by
  decide +kernel

theorem g32p_supplierForest_actual_051360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051360) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_051360
    g32p_supplierForest_actual_051869

def g32p_supplierForest_node_051388 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_051388 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051388 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_060696 := by
  decide +kernel

theorem g32p_supplierForest_actual_051388 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051388) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_051388
    g32p_supplierForest_actual_060696

def g32p_supplierForest_node_051395 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_051395 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051395 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_009483 := by
  decide +kernel

theorem g32p_supplierForest_actual_051395 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051395) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_051395
    g32p_supplierForest_actual_009483

def g32p_supplierForest_node_051399 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_051399 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051399 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_135509 := by
  decide +kernel

theorem g32p_supplierForest_actual_051399 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051399) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 2 g32p_supplierForest_edge_051399
    g32p_supplierForest_actual_135509

def g32p_supplierForest_node_051408 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_051408 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051408 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057367 := by
  decide +kernel

theorem g32p_supplierForest_actual_051408 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051408) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_051408
    g32p_supplierForest_actual_057367

def g32p_supplierForest_node_051410 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_051410 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051410 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_045191 := by
  decide +kernel

theorem g32p_supplierForest_actual_051410 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051410) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_051410
    g32p_supplierForest_actual_045191

def g32p_supplierForest_node_051412 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051412 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051412 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_006836 := by
  decide +kernel

theorem g32p_supplierForest_actual_051412 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051412) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 1 g32p_supplierForest_edge_051412
    g32p_supplierForest_actual_006836

def g32p_supplierForest_node_051416 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_051416 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051416 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_061274 := by
  decide +kernel

theorem g32p_supplierForest_actual_051416 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051416) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_051416
    g32p_supplierForest_actual_061274

def g32p_supplierForest_node_051463 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051463 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051463 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_062916 := by
  decide +kernel

theorem g32p_supplierForest_actual_051463 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051463) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_051463
    g32p_supplierForest_actual_062916

def g32p_supplierForest_node_051469 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051469 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051469 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_048297 := by
  decide +kernel

theorem g32p_supplierForest_actual_051469 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051469) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_051469
    g32p_supplierForest_actual_048297

def g32p_supplierForest_node_051472 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051472 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051472 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_049378 := by
  decide +kernel

theorem g32p_supplierForest_actual_051472 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051472) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_051472
    g32p_supplierForest_actual_049378

def g32p_supplierForest_node_051534 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051534 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_006880 := by
  decide +kernel

theorem g32p_supplierForest_actual_051534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051534) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_051534
    g32p_supplierForest_actual_006880

def g32p_supplierForest_node_051558 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_051558 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051558 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_069392 := by
  decide +kernel

theorem g32p_supplierForest_actual_051558 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051558) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 3 g32p_supplierForest_edge_051558
    g32p_supplierForest_actual_069392

def g32p_supplierForest_node_051573 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_051573 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051573 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_007537 := by
  decide +kernel

theorem g32p_supplierForest_actual_051573 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051573) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_051573
    g32p_supplierForest_actual_007537

def g32p_supplierForest_node_051588 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_051588 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051588 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_052334 := by
  decide +kernel

theorem g32p_supplierForest_actual_051588 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051588) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 1 g32p_supplierForest_edge_051588
    g32p_supplierForest_actual_052334

def g32p_supplierForest_node_051598 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051598 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_051635 := by
  decide +kernel

theorem g32p_supplierForest_actual_051598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051598) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_051598
    g32p_supplierForest_actual_051635

def g32p_supplierForest_node_051618 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051618 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051618 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_049608 := by
  decide +kernel

theorem g32p_supplierForest_actual_051618 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051618) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_051618
    g32p_supplierForest_actual_049608

def g32p_supplierForest_node_051695 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_051695 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051695 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_049156 := by
  decide +kernel

theorem g32p_supplierForest_actual_051695 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051695) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_051695
    g32p_supplierForest_actual_049156

def g32p_supplierForest_node_051805 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_051805 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051805 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_009277 := by
  decide +kernel

theorem g32p_supplierForest_actual_051805 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051805) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_051805
    g32p_supplierForest_actual_009277

def g32p_supplierForest_node_051826 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051826 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051826 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_061065 := by
  decide +kernel

theorem g32p_supplierForest_actual_051826 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051826) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_051826
    g32p_supplierForest_actual_061065

def g32p_supplierForest_node_051834 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_051834 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051834 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064208 := by
  decide +kernel

theorem g32p_supplierForest_actual_051834 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051834) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_051834
    g32p_supplierForest_actual_064208

def g32p_supplierForest_node_051868 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051868 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051868 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_049849 := by
  decide +kernel

theorem g32p_supplierForest_actual_051868 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051868) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_051868
    g32p_supplierForest_actual_049849

def g32p_supplierForest_node_051883 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051883 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051883 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_046495 := by
  decide +kernel

theorem g32p_supplierForest_actual_051883 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051883) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_051883
    g32p_supplierForest_actual_046495

def g32p_supplierForest_node_051892 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_051892 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051892 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_054486 := by
  decide +kernel

theorem g32p_supplierForest_actual_051892 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051892) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_051892
    g32p_supplierForest_actual_054486

def g32p_supplierForest_node_051909 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_051909 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051909 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_054779 := by
  decide +kernel

theorem g32p_supplierForest_actual_051909 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051909) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 1 g32p_supplierForest_edge_051909
    g32p_supplierForest_actual_054779

def g32p_supplierForest_node_051937 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_051937 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051937 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067325 := by
  decide +kernel

theorem g32p_supplierForest_actual_051937 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051937) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_051937
    g32p_supplierForest_actual_067325

def g32p_supplierForest_node_051942 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051942 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051942 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056933 := by
  decide +kernel

theorem g32p_supplierForest_actual_051942 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051942) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_051942
    g32p_supplierForest_actual_056933

def g32p_supplierForest_node_051966 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_051966 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051966 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_007391 := by
  decide +kernel

theorem g32p_supplierForest_actual_051966 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051966) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_051966
    g32p_supplierForest_actual_007391

def g32p_supplierForest_node_052022 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052022 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052022 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_044427 := by
  decide +kernel

theorem g32p_supplierForest_actual_052022 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052022) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 1 g32p_supplierForest_edge_052022
    g32p_supplierForest_actual_044427

def g32p_supplierForest_node_052031 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052031 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052031 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_140055 := by
  decide +kernel

theorem g32p_supplierForest_actual_052031 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052031) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_052031
    g32p_supplierForest_actual_140055

def g32p_supplierForest_node_052129 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_052129 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052129 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_050005 := by
  decide +kernel

theorem g32p_supplierForest_actual_052129 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052129) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_052129
    g32p_supplierForest_actual_050005

def g32p_supplierForest_node_052130 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052130 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052130 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_056147 := by
  decide +kernel

theorem g32p_supplierForest_actual_052130 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052130) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_052130
    g32p_supplierForest_actual_056147

def g32p_supplierForest_node_052145 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_052145 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052145 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_062209 := by
  decide +kernel

theorem g32p_supplierForest_actual_052145 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052145) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 0 g32p_supplierForest_edge_052145
    g32p_supplierForest_actual_062209

def g32p_supplierForest_node_052226 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_052226 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052226 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055539 := by
  decide +kernel

theorem g32p_supplierForest_actual_052226 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052226) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_052226
    g32p_supplierForest_actual_055539

def g32p_supplierForest_node_052249 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052249 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052249 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_059089 := by
  decide +kernel

theorem g32p_supplierForest_actual_052249 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052249) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_052249
    g32p_supplierForest_actual_059089

def g32p_supplierForest_node_052253 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_052253 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052253 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_133958 := by
  decide +kernel

theorem g32p_supplierForest_actual_052253 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052253) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_052253
    g32p_supplierForest_actual_133958

def g32p_supplierForest_node_052299 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_052299 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052299 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_046106 := by
  decide +kernel

theorem g32p_supplierForest_actual_052299 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052299) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_052299
    g32p_supplierForest_actual_046106

def g32p_supplierForest_node_052304 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_052304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052304 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_008272 := by
  decide +kernel

theorem g32p_supplierForest_actual_052304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052304) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_052304
    g32p_supplierForest_actual_008272

def g32p_supplierForest_node_052322 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_052322 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052322 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055159 := by
  decide +kernel

theorem g32p_supplierForest_actual_052322 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052322) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_052322
    g32p_supplierForest_actual_055159

def g32p_supplierForest_node_052325 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052325 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052325 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_007529 := by
  decide +kernel

theorem g32p_supplierForest_actual_052325 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052325) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_052325
    g32p_supplierForest_actual_007529

def g32p_supplierForest_node_052333 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_052333 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052333 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_059922 := by
  decide +kernel

theorem g32p_supplierForest_actual_052333 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052333) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_052333
    g32p_supplierForest_actual_059922

def g32p_supplierForest_node_052337 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052337 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052337 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044427 := by
  decide +kernel

theorem g32p_supplierForest_actual_052337 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052337) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_052337
    g32p_supplierForest_actual_044427

def g32p_supplierForest_node_052349 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052349 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052349 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047757 := by
  decide +kernel

theorem g32p_supplierForest_actual_052349 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052349) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_052349
    g32p_supplierForest_actual_047757

def g32p_supplierForest_node_052372 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_052372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052372 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_056031 := by
  decide +kernel

theorem g32p_supplierForest_actual_052372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052372) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_052372
    g32p_supplierForest_actual_056031

def g32p_supplierForest_node_052389 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052389 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052389 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055167 := by
  decide +kernel

theorem g32p_supplierForest_actual_052389 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052389) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_052389
    g32p_supplierForest_actual_055167

def g32p_supplierForest_node_052427 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052427 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052427 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_059551 := by
  decide +kernel

theorem g32p_supplierForest_actual_052427 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052427) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_052427
    g32p_supplierForest_actual_059551

def g32p_supplierForest_node_052475 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_052475 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052475 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_008296 := by
  decide +kernel

theorem g32p_supplierForest_actual_052475 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052475) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_052475
    g32p_supplierForest_actual_008296

def g32p_supplierForest_node_052484 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052484 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052484 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051910 := by
  decide +kernel

theorem g32p_supplierForest_actual_052484 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052484) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_052484
    g32p_supplierForest_actual_051910

def g32p_supplierForest_node_052499 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_052499 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052499 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056086 := by
  decide +kernel

theorem g32p_supplierForest_actual_052499 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052499) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_052499
    g32p_supplierForest_actual_056086

def g32p_supplierForest_node_052536 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052536 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052536 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_057733 := by
  decide +kernel

theorem g32p_supplierForest_actual_052536 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052536) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_052536
    g32p_supplierForest_actual_057733

def g32p_supplierForest_node_052544 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052544 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052544 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_055185 := by
  decide +kernel

theorem g32p_supplierForest_actual_052544 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052544) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_052544
    g32p_supplierForest_actual_055185

def g32p_supplierForest_node_052560 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_052560 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052560 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047581 := by
  decide +kernel

theorem g32p_supplierForest_actual_052560 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052560) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 1 g32p_supplierForest_edge_052560
    g32p_supplierForest_actual_047581

def g32p_supplierForest_node_052563 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_052563 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052563 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_059218 := by
  decide +kernel

theorem g32p_supplierForest_actual_052563 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052563) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_052563
    g32p_supplierForest_actual_059218

def g32p_supplierForest_node_052573 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_052573 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052573 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_062762 := by
  decide +kernel

theorem g32p_supplierForest_actual_052573 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052573) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_052573
    g32p_supplierForest_actual_062762

def g32p_supplierForest_node_052577 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052577 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052577 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060696 := by
  decide +kernel

theorem g32p_supplierForest_actual_052577 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052577) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_052577
    g32p_supplierForest_actual_060696

def g32p_supplierForest_node_052610 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052610 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052610 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_062811 := by
  decide +kernel

theorem g32p_supplierForest_actual_052610 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052610) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 0 g32p_supplierForest_edge_052610
    g32p_supplierForest_actual_062811

def g32p_supplierForest_node_052625 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_052625 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052625 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_058790 := by
  decide +kernel

theorem g32p_supplierForest_actual_052625 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052625) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 2 g32p_supplierForest_edge_052625
    g32p_supplierForest_actual_058790

def g32p_supplierForest_node_052649 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052649 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052649 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064208 := by
  decide +kernel

theorem g32p_supplierForest_actual_052649 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052649) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 3 g32p_supplierForest_edge_052649
    g32p_supplierForest_actual_064208

def g32p_supplierForest_node_052745 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_052745 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052745 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_136486 := by
  decide +kernel

theorem g32p_supplierForest_actual_052745 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052745) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_052745
    g32p_supplierForest_actual_136486

def g32p_supplierForest_node_052790 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_052790 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052790 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_063037 := by
  decide +kernel

theorem g32p_supplierForest_actual_052790 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052790) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_052790
    g32p_supplierForest_actual_063037

def g32p_supplierForest_node_052822 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_052822 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052822 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_063077 := by
  decide +kernel

theorem g32p_supplierForest_actual_052822 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052822) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_052822
    g32p_supplierForest_actual_063077

def g32p_supplierForest_node_052825 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_052825 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052825 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_048082 := by
  decide +kernel

theorem g32p_supplierForest_actual_052825 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052825) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_052825
    g32p_supplierForest_actual_048082

def g32p_supplierForest_node_052866 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052866 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052866 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_056905 := by
  decide +kernel

theorem g32p_supplierForest_actual_052866 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052866) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 3 g32p_supplierForest_edge_052866
    g32p_supplierForest_actual_056905

def g32p_supplierForest_node_052880 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_052880 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052880 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_046901 := by
  decide +kernel

theorem g32p_supplierForest_actual_052880 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052880) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 2 g32p_supplierForest_edge_052880
    g32p_supplierForest_actual_046901

def g32p_supplierForest_node_052896 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_052896 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052896 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_007742 := by
  decide +kernel

theorem g32p_supplierForest_actual_052896 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052896) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_052896
    g32p_supplierForest_actual_007742

def g32p_supplierForest_node_052898 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052898 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052898 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060830 := by
  decide +kernel

theorem g32p_supplierForest_actual_052898 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052898) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_052898
    g32p_supplierForest_actual_060830

def g32p_supplierForest_node_052903 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_052903 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052903 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_053094 := by
  decide +kernel

theorem g32p_supplierForest_actual_052903 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052903) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_052903
    g32p_supplierForest_actual_053094

def g32p_supplierForest_node_052916 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_052916 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052916 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051543 := by
  decide +kernel

theorem g32p_supplierForest_actual_052916 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052916) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 3 g32p_supplierForest_edge_052916
    g32p_supplierForest_actual_051543

def g32p_supplierForest_node_052918 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052918 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052918 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051715 := by
  decide +kernel

theorem g32p_supplierForest_actual_052918 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052918) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_052918
    g32p_supplierForest_actual_051715

def g32p_supplierForest_node_052925 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052925 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052925 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051483 := by
  decide +kernel

theorem g32p_supplierForest_actual_052925 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052925) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 2 g32p_supplierForest_edge_052925
    g32p_supplierForest_actual_051483

def g32p_supplierForest_node_052990 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052990 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052990 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057201 := by
  decide +kernel

theorem g32p_supplierForest_actual_052990 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052990) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_052990
    g32p_supplierForest_actual_057201

def g32p_supplierForest_node_052994 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_052994 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052994 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_054379 := by
  decide +kernel

theorem g32p_supplierForest_actual_052994 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052994) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 1 g32p_supplierForest_edge_052994
    g32p_supplierForest_actual_054379

def g32p_supplierForest_node_053004 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_053004 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053004 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051059 := by
  decide +kernel

theorem g32p_supplierForest_actual_053004 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053004) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_053004
    g32p_supplierForest_actual_051059

def g32p_supplierForest_node_053028 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_053028 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053028 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_053339 := by
  decide +kernel

theorem g32p_supplierForest_actual_053028 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053028) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 0 g32p_supplierForest_edge_053028
    g32p_supplierForest_actual_053339

def g32p_supplierForest_node_053040 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_053040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053040 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_063306 := by
  decide +kernel

theorem g32p_supplierForest_actual_053040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053040) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_053040
    g32p_supplierForest_actual_063306

def g32p_supplierForest_node_053050 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053050 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053050 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_050132 := by
  decide +kernel

theorem g32p_supplierForest_actual_053050 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053050) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_053050
    g32p_supplierForest_actual_050132

def g32p_supplierForest_node_053075 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_053075 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053075 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_138434 := by
  decide +kernel

theorem g32p_supplierForest_actual_053075 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053075) ∧
        IsConj g (g32p_literalRepresentative 79) := by
  exact g32p_archive_step_lift _ _ 79 3 g32p_supplierForest_edge_053075
    g32p_supplierForest_actual_138434

def g32p_supplierForest_node_053076 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_053076 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053076 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131802 := by
  decide +kernel

theorem g32p_supplierForest_actual_053076 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053076) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_053076
    g32p_supplierForest_actual_131802

def g32p_supplierForest_node_053087 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_053087 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053087 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_127904 := by
  decide +kernel

theorem g32p_supplierForest_actual_053087 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053087) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_053087
    g32p_supplierForest_actual_127904

def g32p_supplierForest_node_053103 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_053103 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053103 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_053515 := by
  decide +kernel

theorem g32p_supplierForest_actual_053103 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053103) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_053103
    g32p_supplierForest_actual_053515

def g32p_supplierForest_node_053138 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_053138 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053138 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_046209 := by
  decide +kernel

theorem g32p_supplierForest_actual_053138 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053138) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_053138
    g32p_supplierForest_actual_046209

def g32p_supplierForest_node_053178 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_053178 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053178 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_055694 := by
  decide +kernel

theorem g32p_supplierForest_actual_053178 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053178) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_053178
    g32p_supplierForest_actual_055694

def g32p_supplierForest_node_053208 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053208 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053208 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_132771 := by
  decide +kernel

theorem g32p_supplierForest_actual_053208 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053208) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_053208
    g32p_supplierForest_actual_132771

def g32p_supplierForest_node_053283 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_053283 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053283 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_011551 := by
  decide +kernel

theorem g32p_supplierForest_actual_053283 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053283) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_053283
    g32p_supplierForest_actual_011551

def g32p_supplierForest_node_053289 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053289 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053289 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057453 := by
  decide +kernel

theorem g32p_supplierForest_actual_053289 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053289) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_053289
    g32p_supplierForest_actual_057453

def g32p_supplierForest_node_053305 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_053305 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053305 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062011 := by
  decide +kernel

theorem g32p_supplierForest_actual_053305 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053305) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 2 g32p_supplierForest_edge_053305
    g32p_supplierForest_actual_062011

def g32p_supplierForest_node_053390 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053390 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053390 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056361 := by
  decide +kernel

theorem g32p_supplierForest_actual_053390 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053390) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 1 g32p_supplierForest_edge_053390
    g32p_supplierForest_actual_056361

def g32p_supplierForest_node_053426 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_053426 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053426 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_044571 := by
  decide +kernel

theorem g32p_supplierForest_actual_053426 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053426) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 1 g32p_supplierForest_edge_053426
    g32p_supplierForest_actual_044571

def g32p_supplierForest_node_053452 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_053452 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053452 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057495 := by
  decide +kernel

theorem g32p_supplierForest_actual_053452 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053452) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_053452
    g32p_supplierForest_actual_057495

def g32p_supplierForest_node_053456 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_053456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053456 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_006732 := by
  decide +kernel

theorem g32p_supplierForest_actual_053456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053456) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_053456
    g32p_supplierForest_actual_006732

def g32p_supplierForest_node_053510 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_053510 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053510 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057625 := by
  decide +kernel

theorem g32p_supplierForest_actual_053510 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053510) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_053510
    g32p_supplierForest_actual_057625

def g32p_supplierForest_node_053524 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_053524 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053524 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_054998 := by
  decide +kernel

theorem g32p_supplierForest_actual_053524 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053524) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_053524
    g32p_supplierForest_actual_054998

def g32p_supplierForest_node_053529 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053529 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_070578 := by
  decide +kernel

theorem g32p_supplierForest_actual_053529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053529) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_053529
    g32p_supplierForest_actual_070578

def g32p_supplierForest_node_053565 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_053565 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053565 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069858 := by
  decide +kernel

theorem g32p_supplierForest_actual_053565 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053565) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_053565
    g32p_supplierForest_actual_069858

def g32p_supplierForest_node_053569 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_053569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053569 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053577 := by
  decide +kernel

theorem g32p_supplierForest_actual_053569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053569) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_053569
    g32p_supplierForest_actual_053577

def g32p_supplierForest_node_053573 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053573 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053573 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_007112 := by
  decide +kernel

theorem g32p_supplierForest_actual_053573 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053573) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_053573
    g32p_supplierForest_actual_007112

def g32p_supplierForest_node_053575 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053575 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053575 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055112 := by
  decide +kernel

theorem g32p_supplierForest_actual_053575 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053575) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_053575
    g32p_supplierForest_actual_055112

def g32p_supplierForest_node_053590 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_053590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053590 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055060 := by
  decide +kernel

theorem g32p_supplierForest_actual_053590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053590) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_053590
    g32p_supplierForest_actual_055060

def g32p_supplierForest_node_053605 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_053605 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053605 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053618 := by
  decide +kernel

theorem g32p_supplierForest_actual_053605 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053605) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_053605
    g32p_supplierForest_actual_053618

def g32p_supplierForest_node_053612 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_053612 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053612 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_053751 := by
  decide +kernel

theorem g32p_supplierForest_actual_053612 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053612) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_053612
    g32p_supplierForest_actual_053751

def g32p_supplierForest_node_053632 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053632 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053632 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012068 := by
  decide +kernel

theorem g32p_supplierForest_actual_053632 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053632) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_053632
    g32p_supplierForest_actual_012068

def g32p_supplierForest_node_053665 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053665 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053665 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_065626 := by
  decide +kernel

theorem g32p_supplierForest_actual_053665 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053665) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 1 g32p_supplierForest_edge_053665
    g32p_supplierForest_actual_065626

def g32p_supplierForest_node_053680 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_053680 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053680 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012148 := by
  decide +kernel

theorem g32p_supplierForest_actual_053680 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053680) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_053680
    g32p_supplierForest_actual_012148

def g32p_supplierForest_node_053715 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_053715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053715 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_139337 := by
  decide +kernel

theorem g32p_supplierForest_actual_053715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053715) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_053715
    g32p_supplierForest_actual_139337

def g32p_supplierForest_node_053718 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_053718 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053718 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_137242 := by
  decide +kernel

theorem g32p_supplierForest_actual_053718 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053718) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 1 g32p_supplierForest_edge_053718
    g32p_supplierForest_actual_137242

def g32p_supplierForest_node_053721 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_053721 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053721 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_064115 := by
  decide +kernel

theorem g32p_supplierForest_actual_053721 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053721) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_053721
    g32p_supplierForest_actual_064115

def g32p_supplierForest_node_053754 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_053754 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053754 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_129309 := by
  decide +kernel

theorem g32p_supplierForest_actual_053754 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053754) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_053754
    g32p_supplierForest_actual_129309

def g32p_supplierForest_node_053800 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053800 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053800 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068002 := by
  decide +kernel

theorem g32p_supplierForest_actual_053800 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053800) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_053800
    g32p_supplierForest_actual_068002

def g32p_supplierForest_node_053833 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_053833 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053833 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064229 := by
  decide +kernel

theorem g32p_supplierForest_actual_053833 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053833) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_053833
    g32p_supplierForest_actual_064229

def g32p_supplierForest_node_053841 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_053841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053841 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055214 := by
  decide +kernel

theorem g32p_supplierForest_actual_053841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053841) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_053841
    g32p_supplierForest_actual_055214

def g32p_supplierForest_node_053902 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_053902 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053902 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_051068 := by
  decide +kernel

theorem g32p_supplierForest_actual_053902 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053902) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_053902
    g32p_supplierForest_actual_051068

def g32p_supplierForest_node_053929 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053929 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053929 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_045294 := by
  decide +kernel

theorem g32p_supplierForest_actual_053929 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053929) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_053929
    g32p_supplierForest_actual_045294

def g32p_supplierForest_node_053950 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053950 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053950 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_130258 := by
  decide +kernel

theorem g32p_supplierForest_actual_053950 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053950) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_053950
    g32p_supplierForest_actual_130258

def g32p_supplierForest_node_053987 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_053987 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053987 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_010141 := by
  decide +kernel

theorem g32p_supplierForest_actual_053987 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053987) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_053987
    g32p_supplierForest_actual_010141

def g32p_supplierForest_node_053988 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_053988 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053988 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_051811 := by
  decide +kernel

theorem g32p_supplierForest_actual_053988 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053988) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_053988
    g32p_supplierForest_actual_051811

def g32p_supplierForest_node_054018 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_054018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054018 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009663 := by
  decide +kernel

theorem g32p_supplierForest_actual_054018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054018) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 0 g32p_supplierForest_edge_054018
    g32p_supplierForest_actual_009663

def g32p_supplierForest_node_054023 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_054023 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054023 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_046425 := by
  decide +kernel

theorem g32p_supplierForest_actual_054023 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054023) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_054023
    g32p_supplierForest_actual_046425

def g32p_supplierForest_node_054030 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_054030 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054030 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_051139 := by
  decide +kernel

theorem g32p_supplierForest_actual_054030 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054030) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_054030
    g32p_supplierForest_actual_051139

def g32p_supplierForest_node_054031 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_054031 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054031 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_064474 := by
  decide +kernel

theorem g32p_supplierForest_actual_054031 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054031) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_054031
    g32p_supplierForest_actual_064474

def g32p_supplierForest_node_054038 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_054038 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054038 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_128471 := by
  decide +kernel

theorem g32p_supplierForest_actual_054038 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054038) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_054038
    g32p_supplierForest_actual_128471

def g32p_supplierForest_node_054045 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054045 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054045 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053979 := by
  decide +kernel

theorem g32p_supplierForest_actual_054045 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054045) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_054045
    g32p_supplierForest_actual_053979

def g32p_supplierForest_node_054059 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054059 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_064517 := by
  decide +kernel

theorem g32p_supplierForest_actual_054059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054059) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_054059
    g32p_supplierForest_actual_064517

def g32p_supplierForest_node_054061 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_054061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054061 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_137368 := by
  decide +kernel

theorem g32p_supplierForest_actual_054061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054061) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_054061
    g32p_supplierForest_actual_137368

def g32p_supplierForest_node_054187 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_054187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054187 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009714 := by
  decide +kernel

theorem g32p_supplierForest_actual_054187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054187) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_054187
    g32p_supplierForest_actual_009714

def g32p_supplierForest_node_054194 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_054194 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054194 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_055159 := by
  decide +kernel

theorem g32p_supplierForest_actual_054194 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054194) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_054194
    g32p_supplierForest_actual_055159

def g32p_supplierForest_node_054231 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_054231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054231 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_062619 := by
  decide +kernel

theorem g32p_supplierForest_actual_054231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054231) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_054231
    g32p_supplierForest_actual_062619

def g32p_supplierForest_node_054234 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054234 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054234 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059548 := by
  decide +kernel

theorem g32p_supplierForest_actual_054234 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054234) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_054234
    g32p_supplierForest_actual_059548

def g32p_supplierForest_node_054254 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054254 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054254 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_055290 := by
  decide +kernel

theorem g32p_supplierForest_actual_054254 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054254) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_054254
    g32p_supplierForest_actual_055290

def g32p_supplierForest_node_054259 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054259 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054259 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_134422 := by
  decide +kernel

theorem g32p_supplierForest_actual_054259 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054259) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_054259
    g32p_supplierForest_actual_134422

def g32p_supplierForest_node_054266 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054266 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054266 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_128258 := by
  decide +kernel

theorem g32p_supplierForest_actual_054266 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054266) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_054266
    g32p_supplierForest_actual_128258

def g32p_supplierForest_node_054290 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054290 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054290 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009751 := by
  decide +kernel

theorem g32p_supplierForest_actual_054290 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054290) ∧
        IsConj g (g32p_literalRepresentative 18) := by
  exact g32p_archive_step_lift _ _ 18 0 g32p_supplierForest_edge_054290
    g32p_supplierForest_actual_009751

def g32p_supplierForest_node_054304 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054304 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_008094 := by
  decide +kernel

theorem g32p_supplierForest_actual_054304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054304) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 1 g32p_supplierForest_edge_054304
    g32p_supplierForest_actual_008094

def g32p_supplierForest_node_054334 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_054334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054334 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_051150 := by
  decide +kernel

theorem g32p_supplierForest_actual_054334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054334) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_054334
    g32p_supplierForest_actual_051150

def g32p_supplierForest_node_054338 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_054338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054338 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_008162 := by
  decide +kernel

theorem g32p_supplierForest_actual_054338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054338) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 1 g32p_supplierForest_edge_054338
    g32p_supplierForest_actual_008162

def g32p_supplierForest_node_054372 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054372 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_062194 := by
  decide +kernel

theorem g32p_supplierForest_actual_054372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054372) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_054372
    g32p_supplierForest_actual_062194

def g32p_supplierForest_node_054470 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054470 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054470 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063590 := by
  decide +kernel

theorem g32p_supplierForest_actual_054470 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054470) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 3 g32p_supplierForest_edge_054470
    g32p_supplierForest_actual_063590

def g32p_supplierForest_node_054471 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054471 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054471 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_128314 := by
  decide +kernel

theorem g32p_supplierForest_actual_054471 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054471) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_054471
    g32p_supplierForest_actual_128314

def g32p_supplierForest_node_054496 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054496 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054496 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067572 := by
  decide +kernel

theorem g32p_supplierForest_actual_054496 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054496) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_054496
    g32p_supplierForest_actual_067572

def g32p_supplierForest_node_054505 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_054505 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054505 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_051780 := by
  decide +kernel

theorem g32p_supplierForest_actual_054505 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054505) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_054505
    g32p_supplierForest_actual_051780

def g32p_supplierForest_node_054507 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054507 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054507 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_046693 := by
  decide +kernel

theorem g32p_supplierForest_actual_054507 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054507) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_054507
    g32p_supplierForest_actual_046693

def g32p_supplierForest_node_054527 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_054527 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054527 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_009837 := by
  decide +kernel

theorem g32p_supplierForest_actual_054527 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054527) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_054527
    g32p_supplierForest_actual_009837

def g32p_supplierForest_node_054528 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_054528 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054528 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_141556 := by
  decide +kernel

theorem g32p_supplierForest_actual_054528 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054528) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 3 g32p_supplierForest_edge_054528
    g32p_supplierForest_actual_141556

def g32p_supplierForest_node_054588 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054588 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054588 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061319 := by
  decide +kernel

theorem g32p_supplierForest_actual_054588 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054588) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_054588
    g32p_supplierForest_actual_061319

def g32p_supplierForest_node_054638 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054638 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_049266 := by
  decide +kernel

theorem g32p_supplierForest_actual_054638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054638) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_054638
    g32p_supplierForest_actual_049266

def g32p_supplierForest_node_054665 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_054665 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054665 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055185 := by
  decide +kernel

theorem g32p_supplierForest_actual_054665 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054665) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_054665
    g32p_supplierForest_actual_055185

def g32p_supplierForest_node_054717 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054717 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054717 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_007346 := by
  decide +kernel

theorem g32p_supplierForest_actual_054717 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054717) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_054717
    g32p_supplierForest_actual_007346

def g32p_supplierForest_node_054749 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054749 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054749 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057196 := by
  decide +kernel

theorem g32p_supplierForest_actual_054749 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054749) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_054749
    g32p_supplierForest_actual_057196

def g32p_supplierForest_node_054751 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_054751 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054751 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057005 := by
  decide +kernel

theorem g32p_supplierForest_actual_054751 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054751) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_054751
    g32p_supplierForest_actual_057005

def g32p_supplierForest_node_054753 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_054753 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054753 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_055837 := by
  decide +kernel

theorem g32p_supplierForest_actual_054753 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054753) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_054753
    g32p_supplierForest_actual_055837

def g32p_supplierForest_node_054798 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_054798 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054798 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065409 := by
  decide +kernel

theorem g32p_supplierForest_actual_054798 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054798) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_054798
    g32p_supplierForest_actual_065409

def g32p_supplierForest_node_054839 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054839 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054839 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_007346 := by
  decide +kernel

theorem g32p_supplierForest_actual_054839 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054839) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_054839
    g32p_supplierForest_actual_007346

def g32p_supplierForest_node_054896 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_054896 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054896 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_007186 := by
  decide +kernel

theorem g32p_supplierForest_actual_054896 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054896) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_054896
    g32p_supplierForest_actual_007186

def g32p_supplierForest_node_054919 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_054919 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054919 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_128238 := by
  decide +kernel

theorem g32p_supplierForest_actual_054919 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054919) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_054919
    g32p_supplierForest_actual_128238

def g32p_supplierForest_node_054964 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_054964 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054964 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044629 := by
  decide +kernel

theorem g32p_supplierForest_actual_054964 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054964) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_054964
    g32p_supplierForest_actual_044629

def g32p_supplierForest_node_054971 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_054971 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054971 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_061259 := by
  decide +kernel

theorem g32p_supplierForest_actual_054971 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054971) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_054971
    g32p_supplierForest_actual_061259

def g32p_supplierForest_node_054993 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_054993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054993 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065627 := by
  decide +kernel

theorem g32p_supplierForest_actual_054993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054993) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_054993
    g32p_supplierForest_actual_065627

def g32p_supplierForest_node_055001 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055001 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055001 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051507 := by
  decide +kernel

theorem g32p_supplierForest_actual_055001 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055001) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_055001
    g32p_supplierForest_actual_051507

def g32p_supplierForest_node_055008 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055008 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055008 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_007684 := by
  decide +kernel

theorem g32p_supplierForest_actual_055008 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055008) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_055008
    g32p_supplierForest_actual_007684

def g32p_supplierForest_node_055011 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_055011 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055011 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_011072 := by
  decide +kernel

theorem g32p_supplierForest_actual_055011 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055011) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_055011
    g32p_supplierForest_actual_011072

def g32p_supplierForest_node_055015 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_055015 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055015 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057393 := by
  decide +kernel

theorem g32p_supplierForest_actual_055015 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055015) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_055015
    g32p_supplierForest_actual_057393

def g32p_supplierForest_node_055024 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_055024 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055024 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065658 := by
  decide +kernel

theorem g32p_supplierForest_actual_055024 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055024) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_055024
    g32p_supplierForest_actual_065658

def g32p_supplierForest_node_055029 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_055029 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055029 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050703 := by
  decide +kernel

theorem g32p_supplierForest_actual_055029 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055029) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 1 g32p_supplierForest_edge_055029
    g32p_supplierForest_actual_050703

def g32p_supplierForest_node_055057 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055057 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_064206 := by
  decide +kernel

theorem g32p_supplierForest_actual_055057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055057) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_055057
    g32p_supplierForest_actual_064206

def g32p_supplierForest_node_055061 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_055061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055061 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_053043 := by
  decide +kernel

theorem g32p_supplierForest_actual_055061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055061) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_055061
    g32p_supplierForest_actual_053043

def g32p_supplierForest_node_055113 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_055113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055113 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_137203 := by
  decide +kernel

theorem g32p_supplierForest_actual_055113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055113) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_055113
    g32p_supplierForest_actual_137203

def g32p_supplierForest_node_055114 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_055114 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055114 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_010068 := by
  decide +kernel

theorem g32p_supplierForest_actual_055114 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055114) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_055114
    g32p_supplierForest_actual_010068

def g32p_supplierForest_node_055160 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_055160 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055160 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044972 := by
  decide +kernel

theorem g32p_supplierForest_actual_055160 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055160) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_055160
    g32p_supplierForest_actual_044972

def g32p_supplierForest_node_055173 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_055173 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055173 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_006715 := by
  decide +kernel

theorem g32p_supplierForest_actual_055173 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055173) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 3 g32p_supplierForest_edge_055173
    g32p_supplierForest_actual_006715

def g32p_supplierForest_node_055247 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_055247 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055247 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_010120 := by
  decide +kernel

theorem g32p_supplierForest_actual_055247 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055247) ∧
        IsConj g (g32p_literalRepresentative 18) := by
  exact g32p_archive_step_lift _ _ 18 0 g32p_supplierForest_edge_055247
    g32p_supplierForest_actual_010120

def g32p_supplierForest_node_055253 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055253 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055253 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065924 := by
  decide +kernel

theorem g32p_supplierForest_actual_055253 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055253) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_055253
    g32p_supplierForest_actual_065924

def g32p_supplierForest_node_055264 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055264 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055264 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065936 := by
  decide +kernel

theorem g32p_supplierForest_actual_055264 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055264) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 0 g32p_supplierForest_edge_055264
    g32p_supplierForest_actual_065936

def g32p_supplierForest_node_055289 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_055289 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055289 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_049375 := by
  decide +kernel

theorem g32p_supplierForest_actual_055289 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055289) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 1 g32p_supplierForest_edge_055289
    g32p_supplierForest_actual_049375

def g32p_supplierForest_node_055299 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_055299 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055299 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012199 := by
  decide +kernel

theorem g32p_supplierForest_actual_055299 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055299) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_055299
    g32p_supplierForest_actual_012199

def g32p_supplierForest_node_055329 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_055329 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055329 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_136186 := by
  decide +kernel

theorem g32p_supplierForest_actual_055329 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055329) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_055329
    g32p_supplierForest_actual_136186

def g32p_supplierForest_node_055342 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_055342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055342 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_010161 := by
  decide +kernel

theorem g32p_supplierForest_actual_055342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055342) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_055342
    g32p_supplierForest_actual_010161

def g32p_supplierForest_node_055388 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055388 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055388 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_051483 := by
  decide +kernel

theorem g32p_supplierForest_actual_055388 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055388) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 1 g32p_supplierForest_edge_055388
    g32p_supplierForest_actual_051483

def g32p_supplierForest_node_055407 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_055407 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055407 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_130392 := by
  decide +kernel

theorem g32p_supplierForest_actual_055407 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055407) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_055407
    g32p_supplierForest_actual_130392

def g32p_supplierForest_node_055426 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_055426 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055426 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_054725 := by
  decide +kernel

theorem g32p_supplierForest_actual_055426 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055426) ∧
        IsConj g (g32p_literalRepresentative 67) := by
  exact g32p_archive_step_lift _ _ 67 2 g32p_supplierForest_edge_055426
    g32p_supplierForest_actual_054725

def g32p_supplierForest_node_055437 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055437 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055437 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_069710 := by
  decide +kernel

theorem g32p_supplierForest_actual_055437 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055437) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_055437
    g32p_supplierForest_actual_069710

def g32p_supplierForest_node_055441 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_055441 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055441 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_066146 := by
  decide +kernel

theorem g32p_supplierForest_actual_055441 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055441) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_055441
    g32p_supplierForest_actual_066146

def g32p_supplierForest_node_055483 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_055483 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055483 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_057005 := by
  decide +kernel

theorem g32p_supplierForest_actual_055483 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055483) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_055483
    g32p_supplierForest_actual_057005

def g32p_supplierForest_node_055489 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_055489 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055489 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056001 := by
  decide +kernel

theorem g32p_supplierForest_actual_055489 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055489) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_055489
    g32p_supplierForest_actual_056001

def g32p_supplierForest_node_055563 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_055563 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055563 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067297 := by
  decide +kernel

theorem g32p_supplierForest_actual_055563 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055563) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_055563
    g32p_supplierForest_actual_067297

def g32p_supplierForest_node_055569 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055569 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009623 := by
  decide +kernel

theorem g32p_supplierForest_actual_055569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055569) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_055569
    g32p_supplierForest_actual_009623

def g32p_supplierForest_node_055578 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055578 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055578 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_044770 := by
  decide +kernel

theorem g32p_supplierForest_actual_055578 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055578) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_055578
    g32p_supplierForest_actual_044770

def g32p_supplierForest_node_055592 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_055592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055592 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_129691 := by
  decide +kernel

theorem g32p_supplierForest_actual_055592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055592) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_055592
    g32p_supplierForest_actual_129691

def g32p_supplierForest_node_055598 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_055598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055598 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_051543 := by
  decide +kernel

theorem g32p_supplierForest_actual_055598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055598) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 1 g32p_supplierForest_edge_055598
    g32p_supplierForest_actual_051543

def g32p_supplierForest_node_055623 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_055623 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055623 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055341 := by
  decide +kernel

theorem g32p_supplierForest_actual_055623 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055623) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_055623
    g32p_supplierForest_actual_055341

def g32p_supplierForest_node_055655 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_055655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055655 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_053607 := by
  decide +kernel

theorem g32p_supplierForest_actual_055655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055655) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_055655
    g32p_supplierForest_actual_053607

def g32p_supplierForest_node_055686 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055686 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_011525 := by
  decide +kernel

theorem g32p_supplierForest_actual_055686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055686) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_055686
    g32p_supplierForest_actual_011525

def g32p_supplierForest_node_055691 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_055691 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055691 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_128778 := by
  decide +kernel

theorem g32p_supplierForest_actual_055691 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055691) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 1 g32p_supplierForest_edge_055691
    g32p_supplierForest_actual_128778

def g32p_supplierForest_node_055693 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055693 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055693 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_053979 := by
  decide +kernel

theorem g32p_supplierForest_actual_055693 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055693) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_055693
    g32p_supplierForest_actual_053979

def g32p_supplierForest_node_055706 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055706 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055706 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061012 := by
  decide +kernel

theorem g32p_supplierForest_actual_055706 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055706) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_055706
    g32p_supplierForest_actual_061012

def g32p_supplierForest_node_055711 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_055711 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055711 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_062240 := by
  decide +kernel

theorem g32p_supplierForest_actual_055711 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055711) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_055711
    g32p_supplierForest_actual_062240

def g32p_supplierForest_node_055725 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_055725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055725 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_054601 := by
  decide +kernel

theorem g32p_supplierForest_actual_055725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055725) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_055725
    g32p_supplierForest_actual_054601

def g32p_supplierForest_node_055741 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_055741 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055741 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066146 := by
  decide +kernel

theorem g32p_supplierForest_actual_055741 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055741) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_055741
    g32p_supplierForest_actual_066146

def g32p_supplierForest_node_055753 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_055753 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055753 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064474 := by
  decide +kernel

theorem g32p_supplierForest_actual_055753 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055753) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_055753
    g32p_supplierForest_actual_064474

def g32p_supplierForest_node_055810 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_055810 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055810 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_060507 := by
  decide +kernel

theorem g32p_supplierForest_actual_055810 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055810) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_055810
    g32p_supplierForest_actual_060507

def g32p_supplierForest_node_055829 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055829 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055829 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055837 := by
  decide +kernel

theorem g32p_supplierForest_actual_055829 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055829) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_055829
    g32p_supplierForest_actual_055837

def g32p_supplierForest_node_055847 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_055847 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055847 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_066619 := by
  decide +kernel

theorem g32p_supplierForest_actual_055847 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055847) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_055847
    g32p_supplierForest_actual_066619

def g32p_supplierForest_node_055871 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_055871 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055871 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_010349 := by
  decide +kernel

theorem g32p_supplierForest_actual_055871 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055871) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 0 g32p_supplierForest_edge_055871
    g32p_supplierForest_actual_010349

def g32p_supplierForest_node_055998 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_055998 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055998 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057495 := by
  decide +kernel

theorem g32p_supplierForest_actual_055998 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055998) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_055998
    g32p_supplierForest_actual_057495

def g32p_supplierForest_node_056025 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056025 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056025 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012275 := by
  decide +kernel

theorem g32p_supplierForest_actual_056025 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056025) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_056025
    g32p_supplierForest_actual_012275

def g32p_supplierForest_node_056027 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_056027 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056027 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_056125 := by
  decide +kernel

theorem g32p_supplierForest_actual_056027 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056027) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_056027
    g32p_supplierForest_actual_056125

def g32p_supplierForest_node_056036 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_056036 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056036 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_052027 := by
  decide +kernel

theorem g32p_supplierForest_actual_056036 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056036) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_056036
    g32p_supplierForest_actual_052027

def g32p_supplierForest_node_056066 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056066 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056066 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_064612 := by
  decide +kernel

theorem g32p_supplierForest_actual_056066 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056066) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_056066
    g32p_supplierForest_actual_064612

def g32p_supplierForest_node_056067 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056067 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056067 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067973 := by
  decide +kernel

theorem g32p_supplierForest_actual_056067 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056067) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_056067
    g32p_supplierForest_actual_067973

def g32p_supplierForest_node_056082 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056082 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056082 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051456 := by
  decide +kernel

theorem g32p_supplierForest_actual_056082 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056082) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_056082
    g32p_supplierForest_actual_051456

def g32p_supplierForest_node_056096 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_056096 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056096 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057733 := by
  decide +kernel

theorem g32p_supplierForest_actual_056096 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056096) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_056096
    g32p_supplierForest_actual_057733

def g32p_supplierForest_node_056133 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_056133 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056133 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057729 := by
  decide +kernel

theorem g32p_supplierForest_actual_056133 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056133) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_056133
    g32p_supplierForest_actual_057729

def g32p_supplierForest_node_056154 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_056154 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056154 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_058534 := by
  decide +kernel

theorem g32p_supplierForest_actual_056154 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056154) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_056154
    g32p_supplierForest_actual_058534

def g32p_supplierForest_node_056155 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056155 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056155 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063894 := by
  decide +kernel

theorem g32p_supplierForest_actual_056155 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056155) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_056155
    g32p_supplierForest_actual_063894

def g32p_supplierForest_node_056172 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_056172 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056172 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067040 := by
  decide +kernel

theorem g32p_supplierForest_actual_056172 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056172) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_056172
    g32p_supplierForest_actual_067040

def g32p_supplierForest_node_056176 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_056176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056176 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068302 := by
  decide +kernel

theorem g32p_supplierForest_actual_056176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056176) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_056176
    g32p_supplierForest_actual_068302

def g32p_supplierForest_node_056194 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_056194 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056194 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071167 := by
  decide +kernel

theorem g32p_supplierForest_actual_056194 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056194) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_056194
    g32p_supplierForest_actual_071167

def g32p_supplierForest_node_056206 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056206 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_066803 := by
  decide +kernel

theorem g32p_supplierForest_actual_056206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056206) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_056206
    g32p_supplierForest_actual_066803

def g32p_supplierForest_node_056215 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_056215 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056215 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067103 := by
  decide +kernel

theorem g32p_supplierForest_actual_056215 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056215) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_056215
    g32p_supplierForest_actual_067103

def g32p_supplierForest_node_056235 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_056235 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056235 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067127 := by
  decide +kernel

theorem g32p_supplierForest_actual_056235 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056235) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 0 g32p_supplierForest_edge_056235
    g32p_supplierForest_actual_067127

def g32p_supplierForest_node_056238 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056238 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_128891 := by
  decide +kernel

theorem g32p_supplierForest_actual_056238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056238) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_056238
    g32p_supplierForest_actual_128891

def g32p_supplierForest_node_056302 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056302 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056302 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069982 := by
  decide +kernel

theorem g32p_supplierForest_actual_056302 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056302) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 1 g32p_supplierForest_edge_056302
    g32p_supplierForest_actual_069982

def g32p_supplierForest_node_056347 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056347 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056347 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_010597 := by
  decide +kernel

theorem g32p_supplierForest_actual_056347 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056347) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 0 g32p_supplierForest_edge_056347
    g32p_supplierForest_actual_010597

def g32p_supplierForest_node_056367 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_056367 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056367 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_010542 := by
  decide +kernel

theorem g32p_supplierForest_actual_056367 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056367) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_056367
    g32p_supplierForest_actual_010542

def g32p_supplierForest_node_056370 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056370 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056370 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_065924 := by
  decide +kernel

theorem g32p_supplierForest_actual_056370 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056370) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_056370
    g32p_supplierForest_actual_065924

def g32p_supplierForest_node_056417 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_056417 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056417 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067325 := by
  decide +kernel

theorem g32p_supplierForest_actual_056417 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056417) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_056417
    g32p_supplierForest_actual_067325

def g32p_supplierForest_node_056449 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056449 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056449 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057608 := by
  decide +kernel

theorem g32p_supplierForest_actual_056449 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056449) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_056449
    g32p_supplierForest_actual_057608

def g32p_supplierForest_node_056461 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_056461 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056461 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071612 := by
  decide +kernel

theorem g32p_supplierForest_actual_056461 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056461) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 1 g32p_supplierForest_edge_056461
    g32p_supplierForest_actual_071612

def g32p_supplierForest_node_056468 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_056468 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056468 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067382 := by
  decide +kernel

theorem g32p_supplierForest_actual_056468 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056468) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_056468
    g32p_supplierForest_actual_067382

def g32p_supplierForest_node_056473 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_056473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056473 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_010590 := by
  decide +kernel

theorem g32p_supplierForest_actual_056473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056473) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 0 g32p_supplierForest_edge_056473
    g32p_supplierForest_actual_010590

def g32p_supplierForest_node_056477 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056477 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056477 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_137161 := by
  decide +kernel

theorem g32p_supplierForest_actual_056477 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056477) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_056477
    g32p_supplierForest_actual_137161

def g32p_supplierForest_node_056528 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_056528 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056528 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067381 := by
  decide +kernel

theorem g32p_supplierForest_actual_056528 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056528) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 0 g32p_supplierForest_edge_056528
    g32p_supplierForest_actual_067381

def g32p_supplierForest_node_056564 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_056564 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056564 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_006686 := by
  decide +kernel

theorem g32p_supplierForest_actual_056564 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056564) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_056564
    g32p_supplierForest_actual_006686

def g32p_supplierForest_node_056603 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_056603 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056603 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044673 := by
  decide +kernel

theorem g32p_supplierForest_actual_056603 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056603) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_056603
    g32p_supplierForest_actual_044673

def g32p_supplierForest_node_056671 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_056671 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056671 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053002 := by
  decide +kernel

theorem g32p_supplierForest_actual_056671 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056671) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_056671
    g32p_supplierForest_actual_053002

def g32p_supplierForest_node_056735 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_056735 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056735 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_134947 := by
  decide +kernel

theorem g32p_supplierForest_actual_056735 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056735) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_056735
    g32p_supplierForest_actual_134947

def g32p_supplierForest_node_056793 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_056793 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056793 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_132430 := by
  decide +kernel

theorem g32p_supplierForest_actual_056793 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056793) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_056793
    g32p_supplierForest_actual_132430

def g32p_supplierForest_node_056801 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_056801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056801 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_052846 := by
  decide +kernel

theorem g32p_supplierForest_actual_056801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056801) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_056801
    g32p_supplierForest_actual_052846

def g32p_supplierForest_node_056803 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056803 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056803 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067772 := by
  decide +kernel

theorem g32p_supplierForest_actual_056803 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056803) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_056803
    g32p_supplierForest_actual_067772

def g32p_supplierForest_node_056810 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_056810 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056810 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065062 := by
  decide +kernel

theorem g32p_supplierForest_actual_056810 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056810) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_056810
    g32p_supplierForest_actual_065062

def g32p_supplierForest_node_056884 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_056884 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056884 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_058544 := by
  decide +kernel

theorem g32p_supplierForest_actual_056884 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056884) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_056884
    g32p_supplierForest_actual_058544

def g32p_supplierForest_node_056897 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056897 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_046425 := by
  decide +kernel

theorem g32p_supplierForest_actual_056897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056897) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_056897
    g32p_supplierForest_actual_046425

def g32p_supplierForest_node_056907 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_056907 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056907 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_007202 := by
  decide +kernel

theorem g32p_supplierForest_actual_056907 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056907) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_056907
    g32p_supplierForest_actual_007202

def g32p_supplierForest_node_056916 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_056916 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056916 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067885 := by
  decide +kernel

theorem g32p_supplierForest_actual_056916 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056916) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_056916
    g32p_supplierForest_actual_067885

def g32p_supplierForest_node_056918 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_056918 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056918 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_053024 := by
  decide +kernel

theorem g32p_supplierForest_actual_056918 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056918) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_056918
    g32p_supplierForest_actual_053024

def g32p_supplierForest_node_056963 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_056963 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056963 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_058534 := by
  decide +kernel

theorem g32p_supplierForest_actual_056963 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056963) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_056963
    g32p_supplierForest_actual_058534

def g32p_supplierForest_node_056968 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_056968 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056968 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067935 := by
  decide +kernel

theorem g32p_supplierForest_actual_056968 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056968) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_056968
    g32p_supplierForest_actual_067935

def g32p_supplierForest_node_056977 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_056977 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056977 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_053200 := by
  decide +kernel

theorem g32p_supplierForest_actual_056977 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056977) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 2 g32p_supplierForest_edge_056977
    g32p_supplierForest_actual_053200

end HodgeLean.Foundations.Program

end
end
