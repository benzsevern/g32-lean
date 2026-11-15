import HodgeLean.Foundations.Program.G32PropFourSixPacked0218
import HodgeLean.Foundations.Program.G32PropFourSixPacked0219
import HodgeLean.Foundations.Program.G32PropFourSixPacked0220
import HodgeLean.Foundations.Program.G32PropFourSixPacked0221
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0212
import HodgeLean.Foundations.Program.G32PropFourSixPacked0213
import HodgeLean.Foundations.Program.G32PropFourSixPacked0215
import HodgeLean.Foundations.Program.G32PropFourSixPacked0216

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_016 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_007270 else g32p_supplierForest_node_007330) else (if i.val < 3 then g32p_supplierForest_node_007339 else g32p_supplierForest_node_007346)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_007363 else g32p_supplierForest_node_007391) else (if i.val < 7 then g32p_supplierForest_node_007418 else g32p_supplierForest_node_007475))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_007522 else g32p_supplierForest_node_007529) else (if i.val < 11 then g32p_supplierForest_node_007537 else g32p_supplierForest_node_007593)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_007597 else g32p_supplierForest_node_007606) else (if i.val < 15 then g32p_supplierForest_node_007684 else g32p_supplierForest_node_007705)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_007713 else g32p_supplierForest_node_007742) else (if i.val < 19 then g32p_supplierForest_node_007749 else g32p_supplierForest_node_007808)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_007844 else g32p_supplierForest_node_007943) else (if i.val < 23 then g32p_supplierForest_node_007946 else g32p_supplierForest_node_007991))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_008017 else g32p_supplierForest_node_008042) else (if i.val < 27 then g32p_supplierForest_node_008045 else g32p_supplierForest_node_008048)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_008058 else g32p_supplierForest_node_008094) else (if i.val < 31 then g32p_supplierForest_node_008111 else g32p_supplierForest_node_008121))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_008162 else g32p_supplierForest_node_008173) else (if i.val < 35 then g32p_supplierForest_node_008272 else g32p_supplierForest_node_008288)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_008293 else g32p_supplierForest_node_008296) else (if i.val < 39 then g32p_supplierForest_node_008332 else g32p_supplierForest_node_008334))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_008365 else g32p_supplierForest_node_008378) else (if i.val < 43 then g32p_supplierForest_node_008431 else g32p_supplierForest_node_008444)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_008547 else g32p_supplierForest_node_008590) else (if i.val < 47 then g32p_supplierForest_node_008599 else g32p_supplierForest_node_008684)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_008776 else g32p_supplierForest_node_008796) else (if i.val < 51 then g32p_supplierForest_node_008832 else g32p_supplierForest_node_008860)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_008862 else g32p_supplierForest_node_008876) else (if i.val < 55 then g32p_supplierForest_node_008881 else g32p_supplierForest_node_008984))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_009005 else g32p_supplierForest_node_009102) else (if i.val < 59 then g32p_supplierForest_node_009114 else g32p_supplierForest_node_009155)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_009197 else g32p_supplierForest_node_009199) else (if i.val < 63 then g32p_supplierForest_node_009252 else g32p_supplierForest_node_009261)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_009263 else g32p_supplierForest_node_009270) else (if i.val < 67 then g32p_supplierForest_node_009277 else g32p_supplierForest_node_009322)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_009346 else g32p_supplierForest_node_009350) else (if i.val < 71 then g32p_supplierForest_node_009351 else g32p_supplierForest_node_009397))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_009449 else g32p_supplierForest_node_009461) else (if i.val < 75 then g32p_supplierForest_node_009483 else g32p_supplierForest_node_009614)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_009623 else g32p_supplierForest_node_009663) else (if i.val < 79 then g32p_supplierForest_node_009666 else g32p_supplierForest_node_009706)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_009714 else g32p_supplierForest_node_009724) else (if i.val < 83 then g32p_supplierForest_node_009733 else g32p_supplierForest_node_009751)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_009774 else g32p_supplierForest_node_009785) else (if i.val < 87 then g32p_supplierForest_node_009791 else g32p_supplierForest_node_009837))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_009842 else g32p_supplierForest_node_009939) else (if i.val < 91 then g32p_supplierForest_node_010055 else g32p_supplierForest_node_010062)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_010068 else g32p_supplierForest_node_010091) else (if i.val < 95 then g32p_supplierForest_node_010120 else g32p_supplierForest_node_010141))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_010142 else g32p_supplierForest_node_010161) else (if i.val < 99 then g32p_supplierForest_node_010203 else g32p_supplierForest_node_010232)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_010233 else g32p_supplierForest_node_010255) else (if i.val < 103 then g32p_supplierForest_node_010288 else g32p_supplierForest_node_010300))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_010349 else g32p_supplierForest_node_010400) else (if i.val < 107 then g32p_supplierForest_node_010437 else g32p_supplierForest_node_010484)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_010527 else g32p_supplierForest_node_010542) else (if i.val < 111 then g32p_supplierForest_node_010556 else g32p_supplierForest_node_010590)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_010591 else g32p_supplierForest_node_010597) else (if i.val < 115 then g32p_supplierForest_node_010631 else g32p_supplierForest_node_010650)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_010655 else g32p_supplierForest_node_010683) else (if i.val < 119 then g32p_supplierForest_node_010684 else g32p_supplierForest_node_010712))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_010737 else g32p_supplierForest_node_010780) else (if i.val < 123 then g32p_supplierForest_node_010792 else g32p_supplierForest_node_010815)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_010824 else g32p_supplierForest_node_010863) else (if i.val < 127 then g32p_supplierForest_node_010959 else g32p_supplierForest_node_011016))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_011040 else g32p_supplierForest_node_011072) else (if i.val < 131 then g32p_supplierForest_node_011101 else g32p_supplierForest_node_011110)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_011120 else g32p_supplierForest_node_011122) else (if i.val < 135 then g32p_supplierForest_node_011188 else g32p_supplierForest_node_011190))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_011195 else g32p_supplierForest_node_011224) else (if i.val < 139 then g32p_supplierForest_node_011362 else g32p_supplierForest_node_011389)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_011390 else g32p_supplierForest_node_011488) else (if i.val < 143 then g32p_supplierForest_node_011497 else g32p_supplierForest_node_011514)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_011525 else g32p_supplierForest_node_011551) else (if i.val < 147 then g32p_supplierForest_node_011560 else g32p_supplierForest_node_011577)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_011599 else g32p_supplierForest_node_011607) else (if i.val < 151 then g32p_supplierForest_node_011713 else g32p_supplierForest_node_011752))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_011825 else g32p_supplierForest_node_011854) else (if i.val < 155 then g32p_supplierForest_node_011862 else g32p_supplierForest_node_011883)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_011933 else g32p_supplierForest_node_011949) else (if i.val < 159 then g32p_supplierForest_node_012000 else g32p_supplierForest_node_012068))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_012095 else g32p_supplierForest_node_012111) else (if i.val < 163 then g32p_supplierForest_node_012148 else g32p_supplierForest_node_012152)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_012174 else g32p_supplierForest_node_012175) else (if i.val < 167 then g32p_supplierForest_node_012184 else g32p_supplierForest_node_012192))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_012199 else g32p_supplierForest_node_012216) else (if i.val < 171 then g32p_supplierForest_node_012249 else g32p_supplierForest_node_012253)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_012275 else g32p_supplierForest_node_012302) else (if i.val < 175 then g32p_supplierForest_node_012348 else g32p_supplierForest_node_012358)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_012367 else g32p_supplierForest_node_012391) else (if i.val < 179 then g32p_supplierForest_node_012406 else g32p_supplierForest_node_012420)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_012454 else g32p_supplierForest_node_012456) else (if i.val < 183 then g32p_supplierForest_node_012511 else g32p_supplierForest_node_012516))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_012559 else g32p_supplierForest_node_012560) else (if i.val < 187 then g32p_supplierForest_node_012562 else g32p_supplierForest_node_012624)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_012660 else g32p_supplierForest_node_012669) else (if i.val < 191 then g32p_supplierForest_node_012675 else g32p_supplierForest_node_012678)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_012744 else g32p_supplierForest_node_012753) else (if i.val < 195 then g32p_supplierForest_node_012772 else g32p_supplierForest_node_012817)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_012846 else g32p_supplierForest_node_012893) else (if i.val < 199 then g32p_supplierForest_node_012903 else g32p_supplierForest_node_012955))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_012993 else g32p_supplierForest_node_013003) else (if i.val < 203 then g32p_supplierForest_node_013026 else g32p_supplierForest_node_013074)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_013108 else g32p_supplierForest_node_013156) else (if i.val < 207 then g32p_supplierForest_node_013175 else g32p_supplierForest_node_013197)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_013216 else g32p_supplierForest_node_013293) else (if i.val < 211 then g32p_supplierForest_node_013294 else g32p_supplierForest_node_013381)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_013504 else g32p_supplierForest_node_013516) else (if i.val < 215 then g32p_supplierForest_node_013592 else g32p_supplierForest_node_013610))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_013622 else g32p_supplierForest_node_013654) else (if i.val < 219 then g32p_supplierForest_node_013752 else g32p_supplierForest_node_013774)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_013897 else g32p_supplierForest_node_013928) else (if i.val < 223 then g32p_supplierForest_node_013943 else g32p_supplierForest_node_013988))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_013994 else g32p_supplierForest_node_014104) else (if i.val < 227 then g32p_supplierForest_node_014154 else g32p_supplierForest_node_014209)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_014215 else g32p_supplierForest_node_014224) else (if i.val < 231 then g32p_supplierForest_node_014256 else g32p_supplierForest_node_014269))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_014296 else g32p_supplierForest_node_014298) else (if i.val < 235 then g32p_supplierForest_node_014303 else g32p_supplierForest_node_014340)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_014371 else g32p_supplierForest_node_014383) else (if i.val < 239 then g32p_supplierForest_node_014395 else g32p_supplierForest_node_014449)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_014454 else g32p_supplierForest_node_014475) else (if i.val < 243 then g32p_supplierForest_node_014481 else g32p_supplierForest_node_014504)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_014507 else g32p_supplierForest_node_014513) else (if i.val < 247 then g32p_supplierForest_node_014522 else g32p_supplierForest_node_014526))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_014548 else g32p_supplierForest_node_014549) else (if i.val < 251 then g32p_supplierForest_node_014561 else g32p_supplierForest_node_014578)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_014581 else g32p_supplierForest_node_014591) else (if i.val < 255 then g32p_supplierForest_node_014676 else g32p_supplierForest_node_014696))))))))

def g32p_supplierForest_classes_016 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 5 else 40) else (if i.val < 3 then 22 else 21)) else (if i.val < 6 then (if i.val < 5 then 24 else 21) else (if i.val < 7 then 7 else 44))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 38) else (if i.val < 11 then 22 else 44)) else (if i.val < 14 then (if i.val < 13 then 44 else 40) else (if i.val < 15 then 7 else 5)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 39 else 20) else (if i.val < 19 then 22 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 38) else (if i.val < 23 then 22 else 5))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 40 else 18) else (if i.val < 27 then 5 else 6)) else (if i.val < 30 then (if i.val < 29 then 6 else 6) else (if i.val < 31 then 40 else 7))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 24 else 24) else (if i.val < 35 then 22 else 24)) else (if i.val < 38 then (if i.val < 37 then 40 else 41) else (if i.val < 39 then 19 else 38))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 22) else (if i.val < 43 then 7 else 22)) else (if i.val < 46 then (if i.val < 45 then 24 else 6) else (if i.val < 47 then 7 else 20)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 18 else 5) else (if i.val < 51 then 5 else 22)) else (if i.val < 54 then (if i.val < 53 then 20 else 39) else (if i.val < 55 then 21 else 39))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 40 else 22) else (if i.val < 59 then 24 else 6)) else (if i.val < 62 then (if i.val < 61 then 7 else 39) else (if i.val < 63 then 19 else 22)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 24 else 5) else (if i.val < 67 then 7 else 24)) else (if i.val < 70 then (if i.val < 69 then 38 else 22) else (if i.val < 71 then 24 else 22))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 7 else 20) else (if i.val < 75 then 22 else 40)) else (if i.val < 78 then (if i.val < 77 then 6 else 6) else (if i.val < 79 then 20 else 41)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 7 else 7) else (if i.val < 83 then 6 else 18)) else (if i.val < 86 then (if i.val < 85 then 6 else 7) else (if i.val < 87 then 7 else 38))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 40 else 21) else (if i.val < 91 then 24 else 38)) else (if i.val < 94 then (if i.val < 93 then 21 else 24) else (if i.val < 95 then 18 else 22))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 24 else 21) else (if i.val < 99 then 21 else 40)) else (if i.val < 102 then (if i.val < 101 then 6 else 24) else (if i.val < 103 then 22 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 20 else 39) else (if i.val < 107 then 7 else 24)) else (if i.val < 110 then (if i.val < 109 then 5 else 22) else (if i.val < 111 then 5 else 6)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 39 else 39) else (if i.val < 115 then 39 else 19)) else (if i.val < 118 then (if i.val < 117 then 24 else 40) else (if i.val < 119 then 39 else 5))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 22 else 24) else (if i.val < 123 then 24 else 21)) else (if i.val < 126 then (if i.val < 125 then 40 else 40) else (if i.val < 127 then 39 else 24))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 20 else 38) else (if i.val < 131 then 24 else 5)) else (if i.val < 134 then (if i.val < 133 then 39 else 22) else (if i.val < 135 then 23 else 22))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 24 else 22) else (if i.val < 139 then 7 else 21)) else (if i.val < 142 then (if i.val < 141 then 40 else 40) else (if i.val < 143 then 19 else 6)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 40 else 22) else (if i.val < 147 then 7 else 24)) else (if i.val < 150 then (if i.val < 149 then 24 else 7) else (if i.val < 151 then 21 else 5))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 7 else 38) else (if i.val < 155 then 40 else 39)) else (if i.val < 158 then (if i.val < 157 then 44 else 20) else (if i.val < 159 then 41 else 7))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 24 else 20) else (if i.val < 163 then 38 else 5)) else (if i.val < 166 then (if i.val < 165 then 19 else 22) else (if i.val < 167 then 22 else 24))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 21 else 24) else (if i.val < 171 then 20 else 21)) else (if i.val < 174 then (if i.val < 173 then 22 else 20) else (if i.val < 175 then 10 else 8)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 9 else 13) else (if i.val < 179 then 10 else 10)) else (if i.val < 182 then (if i.val < 181 then 25 else 45) else (if i.val < 183 then 46 else 10))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 10 else 47) else (if i.val < 187 then 10 else 9)) else (if i.val < 190 then (if i.val < 189 then 9 else 13) else (if i.val < 191 then 48 else 9)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 47 else 25) else (if i.val < 195 then 25 else 10)) else (if i.val < 198 then (if i.val < 197 then 8 else 25) else (if i.val < 199 then 8 else 13))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 12 else 12) else (if i.val < 203 then 25 else 12)) else (if i.val < 206 then (if i.val < 205 then 9 else 10) else (if i.val < 207 then 26 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 47 else 49) else (if i.val < 211 then 46 else 13)) else (if i.val < 214 then (if i.val < 213 then 47 else 48) else (if i.val < 215 then 8 else 26))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 48 else 13) else (if i.val < 219 then 47 else 13)) else (if i.val < 222 then (if i.val < 221 then 13 else 10) else (if i.val < 223 then 27 else 10))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 12 else 10) else (if i.val < 227 then 9 else 13)) else (if i.val < 230 then (if i.val < 229 then 9 else 10) else (if i.val < 231 then 9 else 26))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 10 else 12) else (if i.val < 235 then 27 else 50)) else (if i.val < 238 then (if i.val < 237 then 47 else 46) else (if i.val < 239 then 13 else 10)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 10 else 50) else (if i.val < 243 then 10 else 12)) else (if i.val < 246 then (if i.val < 245 then 49 else 12) else (if i.val < 247 then 47 else 49))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 49) else (if i.val < 251 then 48 else 48)) else (if i.val < 254 then (if i.val < 253 then 49 else 49) else (if i.val < 255 then 50 else 47))))))))

theorem g32p_supplierForest_actual_016 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_016 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_016 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_007270
  · exact g32p_supplierForest_actual_007330
  · exact g32p_supplierForest_actual_007339
  · exact g32p_supplierForest_actual_007346
  · exact g32p_supplierForest_actual_007363
  · exact g32p_supplierForest_actual_007391
  · exact g32p_supplierForest_actual_007418
  · exact g32p_supplierForest_actual_007475
  · exact g32p_supplierForest_actual_007522
  · exact g32p_supplierForest_actual_007529
  · exact g32p_supplierForest_actual_007537
  · exact g32p_supplierForest_actual_007593
  · exact g32p_supplierForest_actual_007597
  · exact g32p_supplierForest_actual_007606
  · exact g32p_supplierForest_actual_007684
  · exact g32p_supplierForest_actual_007705
  · exact g32p_supplierForest_actual_007713
  · exact g32p_supplierForest_actual_007742
  · exact g32p_supplierForest_actual_007749
  · exact g32p_supplierForest_actual_007808
  · exact g32p_supplierForest_actual_007844
  · exact g32p_supplierForest_actual_007943
  · exact g32p_supplierForest_actual_007946
  · exact g32p_supplierForest_actual_007991
  · exact g32p_supplierForest_actual_008017
  · exact g32p_supplierForest_actual_008042
  · exact g32p_supplierForest_actual_008045
  · exact g32p_supplierForest_actual_008048
  · exact g32p_supplierForest_actual_008058
  · exact g32p_supplierForest_actual_008094
  · exact g32p_supplierForest_actual_008111
  · exact g32p_supplierForest_actual_008121
  · exact g32p_supplierForest_actual_008162
  · exact g32p_supplierForest_actual_008173
  · exact g32p_supplierForest_actual_008272
  · exact g32p_supplierForest_actual_008288
  · exact g32p_supplierForest_actual_008293
  · exact g32p_supplierForest_actual_008296
  · exact g32p_supplierForest_actual_008332
  · exact g32p_supplierForest_actual_008334
  · exact g32p_supplierForest_actual_008365
  · exact g32p_supplierForest_actual_008378
  · exact g32p_supplierForest_actual_008431
  · exact g32p_supplierForest_actual_008444
  · exact g32p_supplierForest_actual_008547
  · exact g32p_supplierForest_actual_008590
  · exact g32p_supplierForest_actual_008599
  · exact g32p_supplierForest_actual_008684
  · exact g32p_supplierForest_actual_008776
  · exact g32p_supplierForest_actual_008796
  · exact g32p_supplierForest_actual_008832
  · exact g32p_supplierForest_actual_008860
  · exact g32p_supplierForest_actual_008862
  · exact g32p_supplierForest_actual_008876
  · exact g32p_supplierForest_actual_008881
  · exact g32p_supplierForest_actual_008984
  · exact g32p_supplierForest_actual_009005
  · exact g32p_supplierForest_actual_009102
  · exact g32p_supplierForest_actual_009114
  · exact g32p_supplierForest_actual_009155
  · exact g32p_supplierForest_actual_009197
  · exact g32p_supplierForest_actual_009199
  · exact g32p_supplierForest_actual_009252
  · exact g32p_supplierForest_actual_009261
  · exact g32p_supplierForest_actual_009263
  · exact g32p_supplierForest_actual_009270
  · exact g32p_supplierForest_actual_009277
  · exact g32p_supplierForest_actual_009322
  · exact g32p_supplierForest_actual_009346
  · exact g32p_supplierForest_actual_009350
  · exact g32p_supplierForest_actual_009351
  · exact g32p_supplierForest_actual_009397
  · exact g32p_supplierForest_actual_009449
  · exact g32p_supplierForest_actual_009461
  · exact g32p_supplierForest_actual_009483
  · exact g32p_supplierForest_actual_009614
  · exact g32p_supplierForest_actual_009623
  · exact g32p_supplierForest_actual_009663
  · exact g32p_supplierForest_actual_009666
  · exact g32p_supplierForest_actual_009706
  · exact g32p_supplierForest_actual_009714
  · exact g32p_supplierForest_actual_009724
  · exact g32p_supplierForest_actual_009733
  · exact g32p_supplierForest_actual_009751
  · exact g32p_supplierForest_actual_009774
  · exact g32p_supplierForest_actual_009785
  · exact g32p_supplierForest_actual_009791
  · exact g32p_supplierForest_actual_009837
  · exact g32p_supplierForest_actual_009842
  · exact g32p_supplierForest_actual_009939
  · exact g32p_supplierForest_actual_010055
  · exact g32p_supplierForest_actual_010062
  · exact g32p_supplierForest_actual_010068
  · exact g32p_supplierForest_actual_010091
  · exact g32p_supplierForest_actual_010120
  · exact g32p_supplierForest_actual_010141
  · exact g32p_supplierForest_actual_010142
  · exact g32p_supplierForest_actual_010161
  · exact g32p_supplierForest_actual_010203
  · exact g32p_supplierForest_actual_010232
  · exact g32p_supplierForest_actual_010233
  · exact g32p_supplierForest_actual_010255
  · exact g32p_supplierForest_actual_010288
  · exact g32p_supplierForest_actual_010300
  · exact g32p_supplierForest_actual_010349
  · exact g32p_supplierForest_actual_010400
  · exact g32p_supplierForest_actual_010437
  · exact g32p_supplierForest_actual_010484
  · exact g32p_supplierForest_actual_010527
  · exact g32p_supplierForest_actual_010542
  · exact g32p_supplierForest_actual_010556
  · exact g32p_supplierForest_actual_010590
  · exact g32p_supplierForest_actual_010591
  · exact g32p_supplierForest_actual_010597
  · exact g32p_supplierForest_actual_010631
  · exact g32p_supplierForest_actual_010650
  · exact g32p_supplierForest_actual_010655
  · exact g32p_supplierForest_actual_010683
  · exact g32p_supplierForest_actual_010684
  · exact g32p_supplierForest_actual_010712
  · exact g32p_supplierForest_actual_010737
  · exact g32p_supplierForest_actual_010780
  · exact g32p_supplierForest_actual_010792
  · exact g32p_supplierForest_actual_010815
  · exact g32p_supplierForest_actual_010824
  · exact g32p_supplierForest_actual_010863
  · exact g32p_supplierForest_actual_010959
  · exact g32p_supplierForest_actual_011016
  · exact g32p_supplierForest_actual_011040
  · exact g32p_supplierForest_actual_011072
  · exact g32p_supplierForest_actual_011101
  · exact g32p_supplierForest_actual_011110
  · exact g32p_supplierForest_actual_011120
  · exact g32p_supplierForest_actual_011122
  · exact g32p_supplierForest_actual_011188
  · exact g32p_supplierForest_actual_011190
  · exact g32p_supplierForest_actual_011195
  · exact g32p_supplierForest_actual_011224
  · exact g32p_supplierForest_actual_011362
  · exact g32p_supplierForest_actual_011389
  · exact g32p_supplierForest_actual_011390
  · exact g32p_supplierForest_actual_011488
  · exact g32p_supplierForest_actual_011497
  · exact g32p_supplierForest_actual_011514
  · exact g32p_supplierForest_actual_011525
  · exact g32p_supplierForest_actual_011551
  · exact g32p_supplierForest_actual_011560
  · exact g32p_supplierForest_actual_011577
  · exact g32p_supplierForest_actual_011599
  · exact g32p_supplierForest_actual_011607
  · exact g32p_supplierForest_actual_011713
  · exact g32p_supplierForest_actual_011752
  · exact g32p_supplierForest_actual_011825
  · exact g32p_supplierForest_actual_011854
  · exact g32p_supplierForest_actual_011862
  · exact g32p_supplierForest_actual_011883
  · exact g32p_supplierForest_actual_011933
  · exact g32p_supplierForest_actual_011949
  · exact g32p_supplierForest_actual_012000
  · exact g32p_supplierForest_actual_012068
  · exact g32p_supplierForest_actual_012095
  · exact g32p_supplierForest_actual_012111
  · exact g32p_supplierForest_actual_012148
  · exact g32p_supplierForest_actual_012152
  · exact g32p_supplierForest_actual_012174
  · exact g32p_supplierForest_actual_012175
  · exact g32p_supplierForest_actual_012184
  · exact g32p_supplierForest_actual_012192
  · exact g32p_supplierForest_actual_012199
  · exact g32p_supplierForest_actual_012216
  · exact g32p_supplierForest_actual_012249
  · exact g32p_supplierForest_actual_012253
  · exact g32p_supplierForest_actual_012275
  · exact g32p_supplierForest_actual_012302
  · exact g32p_supplierForest_actual_012348
  · exact g32p_supplierForest_actual_012358
  · exact g32p_supplierForest_actual_012367
  · exact g32p_supplierForest_actual_012391
  · exact g32p_supplierForest_actual_012406
  · exact g32p_supplierForest_actual_012420
  · exact g32p_supplierForest_actual_012454
  · exact g32p_supplierForest_actual_012456
  · exact g32p_supplierForest_actual_012511
  · exact g32p_supplierForest_actual_012516
  · exact g32p_supplierForest_actual_012559
  · exact g32p_supplierForest_actual_012560
  · exact g32p_supplierForest_actual_012562
  · exact g32p_supplierForest_actual_012624
  · exact g32p_supplierForest_actual_012660
  · exact g32p_supplierForest_actual_012669
  · exact g32p_supplierForest_actual_012675
  · exact g32p_supplierForest_actual_012678
  · exact g32p_supplierForest_actual_012744
  · exact g32p_supplierForest_actual_012753
  · exact g32p_supplierForest_actual_012772
  · exact g32p_supplierForest_actual_012817
  · exact g32p_supplierForest_actual_012846
  · exact g32p_supplierForest_actual_012893
  · exact g32p_supplierForest_actual_012903
  · exact g32p_supplierForest_actual_012955
  · exact g32p_supplierForest_actual_012993
  · exact g32p_supplierForest_actual_013003
  · exact g32p_supplierForest_actual_013026
  · exact g32p_supplierForest_actual_013074
  · exact g32p_supplierForest_actual_013108
  · exact g32p_supplierForest_actual_013156
  · exact g32p_supplierForest_actual_013175
  · exact g32p_supplierForest_actual_013197
  · exact g32p_supplierForest_actual_013216
  · exact g32p_supplierForest_actual_013293
  · exact g32p_supplierForest_actual_013294
  · exact g32p_supplierForest_actual_013381
  · exact g32p_supplierForest_actual_013504
  · exact g32p_supplierForest_actual_013516
  · exact g32p_supplierForest_actual_013592
  · exact g32p_supplierForest_actual_013610
  · exact g32p_supplierForest_actual_013622
  · exact g32p_supplierForest_actual_013654
  · exact g32p_supplierForest_actual_013752
  · exact g32p_supplierForest_actual_013774
  · exact g32p_supplierForest_actual_013897
  · exact g32p_supplierForest_actual_013928
  · exact g32p_supplierForest_actual_013943
  · exact g32p_supplierForest_actual_013988
  · exact g32p_supplierForest_actual_013994
  · exact g32p_supplierForest_actual_014104
  · exact g32p_supplierForest_actual_014154
  · exact g32p_supplierForest_actual_014209
  · exact g32p_supplierForest_actual_014215
  · exact g32p_supplierForest_actual_014224
  · exact g32p_supplierForest_actual_014256
  · exact g32p_supplierForest_actual_014269
  · exact g32p_supplierForest_actual_014296
  · exact g32p_supplierForest_actual_014298
  · exact g32p_supplierForest_actual_014303
  · exact g32p_supplierForest_actual_014340
  · exact g32p_supplierForest_actual_014371
  · exact g32p_supplierForest_actual_014383
  · exact g32p_supplierForest_actual_014395
  · exact g32p_supplierForest_actual_014449
  · exact g32p_supplierForest_actual_014454
  · exact g32p_supplierForest_actual_014475
  · exact g32p_supplierForest_actual_014481
  · exact g32p_supplierForest_actual_014504
  · exact g32p_supplierForest_actual_014507
  · exact g32p_supplierForest_actual_014513
  · exact g32p_supplierForest_actual_014522
  · exact g32p_supplierForest_actual_014526
  · exact g32p_supplierForest_actual_014548
  · exact g32p_supplierForest_actual_014549
  · exact g32p_supplierForest_actual_014561
  · exact g32p_supplierForest_actual_014578
  · exact g32p_supplierForest_actual_014581
  · exact g32p_supplierForest_actual_014591
  · exact g32p_supplierForest_actual_014676
  · exact g32p_supplierForest_actual_014696

def g32p_supplierForest_nodes_017 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_014731 else g32p_supplierForest_node_014760) else (if i.val < 3 then g32p_supplierForest_node_014764 else g32p_supplierForest_node_014817)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_014822 else g32p_supplierForest_node_014824) else (if i.val < 7 then g32p_supplierForest_node_014832 else g32p_supplierForest_node_014852))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_014859 else g32p_supplierForest_node_014873) else (if i.val < 11 then g32p_supplierForest_node_014875 else g32p_supplierForest_node_014897)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_014919 else g32p_supplierForest_node_014938) else (if i.val < 15 then g32p_supplierForest_node_014975 else g32p_supplierForest_node_015112)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_015136 else g32p_supplierForest_node_015138) else (if i.val < 19 then g32p_supplierForest_node_015149 else g32p_supplierForest_node_015150)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_015183 else g32p_supplierForest_node_015191) else (if i.val < 23 then g32p_supplierForest_node_015207 else g32p_supplierForest_node_015223))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_015300 else g32p_supplierForest_node_015314) else (if i.val < 27 then g32p_supplierForest_node_015326 else g32p_supplierForest_node_015352)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_015371 else g32p_supplierForest_node_015378) else (if i.val < 31 then g32p_supplierForest_node_015435 else g32p_supplierForest_node_015456))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_015482 else g32p_supplierForest_node_015507) else (if i.val < 35 then g32p_supplierForest_node_015522 else g32p_supplierForest_node_015634)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_015648 else g32p_supplierForest_node_015657) else (if i.val < 39 then g32p_supplierForest_node_015715 else g32p_supplierForest_node_015740))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_015747 else g32p_supplierForest_node_015832) else (if i.val < 43 then g32p_supplierForest_node_015840 else g32p_supplierForest_node_015862)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_015871 else g32p_supplierForest_node_015896) else (if i.val < 47 then g32p_supplierForest_node_015943 else g32p_supplierForest_node_015945)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_015951 else g32p_supplierForest_node_015954) else (if i.val < 51 then g32p_supplierForest_node_015992 else g32p_supplierForest_node_015996)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_016041 else g32p_supplierForest_node_016065) else (if i.val < 55 then g32p_supplierForest_node_016074 else g32p_supplierForest_node_016084))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_016094 else g32p_supplierForest_node_016131) else (if i.val < 59 then g32p_supplierForest_node_016137 else g32p_supplierForest_node_016176)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_016183 else g32p_supplierForest_node_016217) else (if i.val < 63 then g32p_supplierForest_node_016238 else g32p_supplierForest_node_016268)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_016280 else g32p_supplierForest_node_016297) else (if i.val < 67 then g32p_supplierForest_node_016322 else g32p_supplierForest_node_016328)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_016336 else g32p_supplierForest_node_016353) else (if i.val < 71 then g32p_supplierForest_node_016364 else g32p_supplierForest_node_016367))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_016374 else g32p_supplierForest_node_016396) else (if i.val < 75 then g32p_supplierForest_node_016406 else g32p_supplierForest_node_016417)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_016448 else g32p_supplierForest_node_016552) else (if i.val < 79 then g32p_supplierForest_node_016571 else g32p_supplierForest_node_016586)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_016615 else g32p_supplierForest_node_016657) else (if i.val < 83 then g32p_supplierForest_node_016666 else g32p_supplierForest_node_016693)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_016701 else g32p_supplierForest_node_016733) else (if i.val < 87 then g32p_supplierForest_node_016771 else g32p_supplierForest_node_016788))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_016819 else g32p_supplierForest_node_016869) else (if i.val < 91 then g32p_supplierForest_node_016935 else g32p_supplierForest_node_017008)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_017150 else g32p_supplierForest_node_017210) else (if i.val < 95 then g32p_supplierForest_node_017245 else g32p_supplierForest_node_017266))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_017394 else g32p_supplierForest_node_017413) else (if i.val < 99 then g32p_supplierForest_node_017482 else g32p_supplierForest_node_017508)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_017511 else g32p_supplierForest_node_017698) else (if i.val < 103 then g32p_supplierForest_node_017711 else g32p_supplierForest_node_017810))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_017828 else g32p_supplierForest_node_017835) else (if i.val < 107 then g32p_supplierForest_node_017980 else g32p_supplierForest_node_017982)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_018004 else g32p_supplierForest_node_018013) else (if i.val < 111 then g32p_supplierForest_node_018058 else g32p_supplierForest_node_018083)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_018087 else g32p_supplierForest_node_018094) else (if i.val < 115 then g32p_supplierForest_node_018122 else g32p_supplierForest_node_018128)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_018204 else g32p_supplierForest_node_018222) else (if i.val < 119 then g32p_supplierForest_node_018334 else g32p_supplierForest_node_018350))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_018352 else g32p_supplierForest_node_018378) else (if i.val < 123 then g32p_supplierForest_node_018384 else g32p_supplierForest_node_018445)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_018448 else g32p_supplierForest_node_018451) else (if i.val < 127 then g32p_supplierForest_node_018472 else g32p_supplierForest_node_018487))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_018542 else g32p_supplierForest_node_018547) else (if i.val < 131 then g32p_supplierForest_node_018597 else g32p_supplierForest_node_018637)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_018664 else g32p_supplierForest_node_018715) else (if i.val < 135 then g32p_supplierForest_node_018740 else g32p_supplierForest_node_018813))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_018888 else g32p_supplierForest_node_018897) else (if i.val < 139 then g32p_supplierForest_node_018938 else g32p_supplierForest_node_018955)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_018986 else g32p_supplierForest_node_019033) else (if i.val < 143 then g32p_supplierForest_node_019081 else g32p_supplierForest_node_019103)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_019120 else g32p_supplierForest_node_019122) else (if i.val < 147 then g32p_supplierForest_node_019138 else g32p_supplierForest_node_019146)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_019158 else g32p_supplierForest_node_019174) else (if i.val < 151 then g32p_supplierForest_node_019212 else g32p_supplierForest_node_019245))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_019246 else g32p_supplierForest_node_019257) else (if i.val < 155 then g32p_supplierForest_node_019263 else g32p_supplierForest_node_019311)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_019337 else g32p_supplierForest_node_019345) else (if i.val < 159 then g32p_supplierForest_node_019421 else g32p_supplierForest_node_019452))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_019469 else g32p_supplierForest_node_019484) else (if i.val < 163 then g32p_supplierForest_node_019514 else g32p_supplierForest_node_019527)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_019565 else g32p_supplierForest_node_019567) else (if i.val < 167 then g32p_supplierForest_node_019631 else g32p_supplierForest_node_019661))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_019663 else g32p_supplierForest_node_019665) else (if i.val < 171 then g32p_supplierForest_node_019675 else g32p_supplierForest_node_019694)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_019696 else g32p_supplierForest_node_019714) else (if i.val < 175 then g32p_supplierForest_node_019727 else g32p_supplierForest_node_019781)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_019844 else g32p_supplierForest_node_019857) else (if i.val < 179 then g32p_supplierForest_node_019943 else g32p_supplierForest_node_019946)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_019947 else g32p_supplierForest_node_020016) else (if i.val < 183 then g32p_supplierForest_node_020023 else g32p_supplierForest_node_020056))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_020067 else g32p_supplierForest_node_020115) else (if i.val < 187 then g32p_supplierForest_node_020125 else g32p_supplierForest_node_020157)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_020170 else g32p_supplierForest_node_020171) else (if i.val < 191 then g32p_supplierForest_node_020178 else g32p_supplierForest_node_020195)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_020227 else g32p_supplierForest_node_020233) else (if i.val < 195 then g32p_supplierForest_node_020246 else g32p_supplierForest_node_020295)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_020298 else g32p_supplierForest_node_020304) else (if i.val < 199 then g32p_supplierForest_node_020332 else g32p_supplierForest_node_020376))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_020418 else g32p_supplierForest_node_020448) else (if i.val < 203 then g32p_supplierForest_node_020457 else g32p_supplierForest_node_020474)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_020478 else g32p_supplierForest_node_020482) else (if i.val < 207 then g32p_supplierForest_node_020523 else g32p_supplierForest_node_020588)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_020594 else g32p_supplierForest_node_020622) else (if i.val < 211 then g32p_supplierForest_node_020654 else g32p_supplierForest_node_020695)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_020704 else g32p_supplierForest_node_020706) else (if i.val < 215 then g32p_supplierForest_node_020717 else g32p_supplierForest_node_020791))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_020792 else g32p_supplierForest_node_020794) else (if i.val < 219 then g32p_supplierForest_node_020894 else g32p_supplierForest_node_020922)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_020950 else g32p_supplierForest_node_020996) else (if i.val < 223 then g32p_supplierForest_node_021005 else g32p_supplierForest_node_021046))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_021058 else g32p_supplierForest_node_021077) else (if i.val < 227 then g32p_supplierForest_node_021080 else g32p_supplierForest_node_021085)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_021091 else g32p_supplierForest_node_021118) else (if i.val < 231 then g32p_supplierForest_node_021138 else g32p_supplierForest_node_021143))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_021155 else g32p_supplierForest_node_021182) else (if i.val < 235 then g32p_supplierForest_node_021248 else g32p_supplierForest_node_021251)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_021257 else g32p_supplierForest_node_021294) else (if i.val < 239 then g32p_supplierForest_node_021321 else g32p_supplierForest_node_021338)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_021350 else g32p_supplierForest_node_021398) else (if i.val < 243 then g32p_supplierForest_node_021403 else g32p_supplierForest_node_021449)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_021451 else g32p_supplierForest_node_021469) else (if i.val < 247 then g32p_supplierForest_node_021476 else g32p_supplierForest_node_021512))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_021517 else g32p_supplierForest_node_021537) else (if i.val < 251 then g32p_supplierForest_node_021546 else g32p_supplierForest_node_021549)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_021563 else g32p_supplierForest_node_021597) else (if i.val < 255 then g32p_supplierForest_node_021624 else g32p_supplierForest_node_021633))))))))

def g32p_supplierForest_classes_017 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 10 else 51) else (if i.val < 3 then 51 else 49)) else (if i.val < 6 then (if i.val < 5 then 49 else 47) else (if i.val < 7 then 49 else 50))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 48) else (if i.val < 11 then 27 else 47)) else (if i.val < 14 then (if i.val < 13 then 26 else 49) else (if i.val < 15 then 27 else 50)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 12 else 13) else (if i.val < 19 then 46 else 49)) else (if i.val < 22 then (if i.val < 21 then 8 else 26) else (if i.val < 23 then 27 else 1))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 8 else 26) else (if i.val < 27 then 51 else 47)) else (if i.val < 30 then (if i.val < 29 then 13 else 51) else (if i.val < 31 then 12 else 9))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 50 else 50) else (if i.val < 35 then 9 else 25)) else (if i.val < 38 then (if i.val < 37 then 50 else 25) else (if i.val < 39 then 26 else 50))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 54 else 47) else (if i.val < 43 then 48 else 51)) else (if i.val < 46 then (if i.val < 45 then 9 else 13) else (if i.val < 47 then 27 else 10)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 49) else (if i.val < 51 then 51 else 27)) else (if i.val < 54 then (if i.val < 53 then 10 else 51) else (if i.val < 55 then 9 else 47))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 51 else 47) else (if i.val < 59 then 28 else 49)) else (if i.val < 62 then (if i.val < 61 then 48 else 51) else (if i.val < 63 then 50 else 25)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 48 else 47) else (if i.val < 67 then 48 else 47)) else (if i.val < 70 then (if i.val < 69 then 51 else 12) else (if i.val < 71 then 50 else 49))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 51 else 47) else (if i.val < 75 then 8 else 49)) else (if i.val < 78 then (if i.val < 77 then 13 else 46) else (if i.val < 79 then 51 else 56)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 51 else 51) else (if i.val < 83 then 49 else 25)) else (if i.val < 86 then (if i.val < 85 then 13 else 49) else (if i.val < 87 then 12 else 46))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 47 else 13) else (if i.val < 91 then 9 else 12)) else (if i.val < 94 then (if i.val < 93 then 28 else 13) else (if i.val < 95 then 49 else 13))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 13 else 27) else (if i.val < 99 then 46 else 28)) else (if i.val < 102 then (if i.val < 101 then 48 else 27) else (if i.val < 103 then 26 else 26))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 27 else 9) else (if i.val < 107 then 10 else 48)) else (if i.val < 110 then (if i.val < 109 then 49 else 11) else (if i.val < 111 then 13 else 47)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 12 else 47) else (if i.val < 115 then 50 else 50)) else (if i.val < 118 then (if i.val < 117 then 47 else 50) else (if i.val < 119 then 8 else 25))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 46 else 47) else (if i.val < 123 then 10 else 10)) else (if i.val < 126 then (if i.val < 125 then 12 else 8) else (if i.val < 127 then 47 else 12))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 27 else 51) else (if i.val < 131 then 26 else 50)) else (if i.val < 134 then (if i.val < 133 then 13 else 47) else (if i.val < 135 then 26 else 10))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 10 else 12) else (if i.val < 139 then 13 else 27)) else (if i.val < 142 then (if i.val < 141 then 27 else 11) else (if i.val < 143 then 13 else 10)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 49 else 9) else (if i.val < 147 then 13 else 9)) else (if i.val < 150 then (if i.val < 149 then 10 else 10) else (if i.val < 151 then 10 else 8))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 9 else 47) else (if i.val < 155 then 48 else 47)) else (if i.val < 158 then (if i.val < 157 then 13 else 1) else (if i.val < 159 then 13 else 12))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 13 else 27) else (if i.val < 163 then 27 else 8)) else (if i.val < 166 then (if i.val < 165 then 50 else 10) else (if i.val < 167 then 27 else 26))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 12 else 10) else (if i.val < 171 then 48 else 50)) else (if i.val < 174 then (if i.val < 173 then 48 else 26) else (if i.val < 175 then 27 else 9)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 13 else 12) else (if i.val < 179 then 9 else 27)) else (if i.val < 182 then (if i.val < 181 then 11 else 25) else (if i.val < 183 then 9 else 25))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 12 else 13) else (if i.val < 187 then 11 else 11)) else (if i.val < 190 then (if i.val < 189 then 12 else 49) else (if i.val < 191 then 53 else 13)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 48 else 47) else (if i.val < 195 then 25 else 46)) else (if i.val < 198 then (if i.val < 197 then 50 else 47) else (if i.val < 199 then 49 else 9))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 12 else 26) else (if i.val < 203 then 12 else 48)) else (if i.val < 206 then (if i.val < 205 then 47 else 48) else (if i.val < 207 then 48 else 26)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 13 else 26) else (if i.val < 211 then 26 else 46)) else (if i.val < 214 then (if i.val < 213 then 50 else 50) else (if i.val < 215 then 54 else 27))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 27 else 10) else (if i.val < 219 then 25 else 51)) else (if i.val < 222 then (if i.val < 221 then 25 else 49) else (if i.val < 223 then 13 else 11))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 27 else 47) else (if i.val < 227 then 50 else 48)) else (if i.val < 230 then (if i.val < 229 then 8 else 50) else (if i.val < 231 then 9 else 51))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 51 else 26) else (if i.val < 235 then 47 else 49)) else (if i.val < 238 then (if i.val < 237 then 51 else 9) else (if i.val < 239 then 51 else 50)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 10) else (if i.val < 243 then 12 else 48)) else (if i.val < 246 then (if i.val < 245 then 50 else 26) else (if i.val < 247 then 8 else 27))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 46 else 47) else (if i.val < 251 then 9 else 13)) else (if i.val < 254 then (if i.val < 253 then 47 else 49) else (if i.val < 255 then 46 else 48))))))))

theorem g32p_supplierForest_actual_017 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_017 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_017 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_014731
  · exact g32p_supplierForest_actual_014760
  · exact g32p_supplierForest_actual_014764
  · exact g32p_supplierForest_actual_014817
  · exact g32p_supplierForest_actual_014822
  · exact g32p_supplierForest_actual_014824
  · exact g32p_supplierForest_actual_014832
  · exact g32p_supplierForest_actual_014852
  · exact g32p_supplierForest_actual_014859
  · exact g32p_supplierForest_actual_014873
  · exact g32p_supplierForest_actual_014875
  · exact g32p_supplierForest_actual_014897
  · exact g32p_supplierForest_actual_014919
  · exact g32p_supplierForest_actual_014938
  · exact g32p_supplierForest_actual_014975
  · exact g32p_supplierForest_actual_015112
  · exact g32p_supplierForest_actual_015136
  · exact g32p_supplierForest_actual_015138
  · exact g32p_supplierForest_actual_015149
  · exact g32p_supplierForest_actual_015150
  · exact g32p_supplierForest_actual_015183
  · exact g32p_supplierForest_actual_015191
  · exact g32p_supplierForest_actual_015207
  · exact g32p_supplierForest_actual_015223
  · exact g32p_supplierForest_actual_015300
  · exact g32p_supplierForest_actual_015314
  · exact g32p_supplierForest_actual_015326
  · exact g32p_supplierForest_actual_015352
  · exact g32p_supplierForest_actual_015371
  · exact g32p_supplierForest_actual_015378
  · exact g32p_supplierForest_actual_015435
  · exact g32p_supplierForest_actual_015456
  · exact g32p_supplierForest_actual_015482
  · exact g32p_supplierForest_actual_015507
  · exact g32p_supplierForest_actual_015522
  · exact g32p_supplierForest_actual_015634
  · exact g32p_supplierForest_actual_015648
  · exact g32p_supplierForest_actual_015657
  · exact g32p_supplierForest_actual_015715
  · exact g32p_supplierForest_actual_015740
  · exact g32p_supplierForest_actual_015747
  · exact g32p_supplierForest_actual_015832
  · exact g32p_supplierForest_actual_015840
  · exact g32p_supplierForest_actual_015862
  · exact g32p_supplierForest_actual_015871
  · exact g32p_supplierForest_actual_015896
  · exact g32p_supplierForest_actual_015943
  · exact g32p_supplierForest_actual_015945
  · exact g32p_supplierForest_actual_015951
  · exact g32p_supplierForest_actual_015954
  · exact g32p_supplierForest_actual_015992
  · exact g32p_supplierForest_actual_015996
  · exact g32p_supplierForest_actual_016041
  · exact g32p_supplierForest_actual_016065
  · exact g32p_supplierForest_actual_016074
  · exact g32p_supplierForest_actual_016084
  · exact g32p_supplierForest_actual_016094
  · exact g32p_supplierForest_actual_016131
  · exact g32p_supplierForest_actual_016137
  · exact g32p_supplierForest_actual_016176
  · exact g32p_supplierForest_actual_016183
  · exact g32p_supplierForest_actual_016217
  · exact g32p_supplierForest_actual_016238
  · exact g32p_supplierForest_actual_016268
  · exact g32p_supplierForest_actual_016280
  · exact g32p_supplierForest_actual_016297
  · exact g32p_supplierForest_actual_016322
  · exact g32p_supplierForest_actual_016328
  · exact g32p_supplierForest_actual_016336
  · exact g32p_supplierForest_actual_016353
  · exact g32p_supplierForest_actual_016364
  · exact g32p_supplierForest_actual_016367
  · exact g32p_supplierForest_actual_016374
  · exact g32p_supplierForest_actual_016396
  · exact g32p_supplierForest_actual_016406
  · exact g32p_supplierForest_actual_016417
  · exact g32p_supplierForest_actual_016448
  · exact g32p_supplierForest_actual_016552
  · exact g32p_supplierForest_actual_016571
  · exact g32p_supplierForest_actual_016586
  · exact g32p_supplierForest_actual_016615
  · exact g32p_supplierForest_actual_016657
  · exact g32p_supplierForest_actual_016666
  · exact g32p_supplierForest_actual_016693
  · exact g32p_supplierForest_actual_016701
  · exact g32p_supplierForest_actual_016733
  · exact g32p_supplierForest_actual_016771
  · exact g32p_supplierForest_actual_016788
  · exact g32p_supplierForest_actual_016819
  · exact g32p_supplierForest_actual_016869
  · exact g32p_supplierForest_actual_016935
  · exact g32p_supplierForest_actual_017008
  · exact g32p_supplierForest_actual_017150
  · exact g32p_supplierForest_actual_017210
  · exact g32p_supplierForest_actual_017245
  · exact g32p_supplierForest_actual_017266
  · exact g32p_supplierForest_actual_017394
  · exact g32p_supplierForest_actual_017413
  · exact g32p_supplierForest_actual_017482
  · exact g32p_supplierForest_actual_017508
  · exact g32p_supplierForest_actual_017511
  · exact g32p_supplierForest_actual_017698
  · exact g32p_supplierForest_actual_017711
  · exact g32p_supplierForest_actual_017810
  · exact g32p_supplierForest_actual_017828
  · exact g32p_supplierForest_actual_017835
  · exact g32p_supplierForest_actual_017980
  · exact g32p_supplierForest_actual_017982
  · exact g32p_supplierForest_actual_018004
  · exact g32p_supplierForest_actual_018013
  · exact g32p_supplierForest_actual_018058
  · exact g32p_supplierForest_actual_018083
  · exact g32p_supplierForest_actual_018087
  · exact g32p_supplierForest_actual_018094
  · exact g32p_supplierForest_actual_018122
  · exact g32p_supplierForest_actual_018128
  · exact g32p_supplierForest_actual_018204
  · exact g32p_supplierForest_actual_018222
  · exact g32p_supplierForest_actual_018334
  · exact g32p_supplierForest_actual_018350
  · exact g32p_supplierForest_actual_018352
  · exact g32p_supplierForest_actual_018378
  · exact g32p_supplierForest_actual_018384
  · exact g32p_supplierForest_actual_018445
  · exact g32p_supplierForest_actual_018448
  · exact g32p_supplierForest_actual_018451
  · exact g32p_supplierForest_actual_018472
  · exact g32p_supplierForest_actual_018487
  · exact g32p_supplierForest_actual_018542
  · exact g32p_supplierForest_actual_018547
  · exact g32p_supplierForest_actual_018597
  · exact g32p_supplierForest_actual_018637
  · exact g32p_supplierForest_actual_018664
  · exact g32p_supplierForest_actual_018715
  · exact g32p_supplierForest_actual_018740
  · exact g32p_supplierForest_actual_018813
  · exact g32p_supplierForest_actual_018888
  · exact g32p_supplierForest_actual_018897
  · exact g32p_supplierForest_actual_018938
  · exact g32p_supplierForest_actual_018955
  · exact g32p_supplierForest_actual_018986
  · exact g32p_supplierForest_actual_019033
  · exact g32p_supplierForest_actual_019081
  · exact g32p_supplierForest_actual_019103
  · exact g32p_supplierForest_actual_019120
  · exact g32p_supplierForest_actual_019122
  · exact g32p_supplierForest_actual_019138
  · exact g32p_supplierForest_actual_019146
  · exact g32p_supplierForest_actual_019158
  · exact g32p_supplierForest_actual_019174
  · exact g32p_supplierForest_actual_019212
  · exact g32p_supplierForest_actual_019245
  · exact g32p_supplierForest_actual_019246
  · exact g32p_supplierForest_actual_019257
  · exact g32p_supplierForest_actual_019263
  · exact g32p_supplierForest_actual_019311
  · exact g32p_supplierForest_actual_019337
  · exact g32p_supplierForest_actual_019345
  · exact g32p_supplierForest_actual_019421
  · exact g32p_supplierForest_actual_019452
  · exact g32p_supplierForest_actual_019469
  · exact g32p_supplierForest_actual_019484
  · exact g32p_supplierForest_actual_019514
  · exact g32p_supplierForest_actual_019527
  · exact g32p_supplierForest_actual_019565
  · exact g32p_supplierForest_actual_019567
  · exact g32p_supplierForest_actual_019631
  · exact g32p_supplierForest_actual_019661
  · exact g32p_supplierForest_actual_019663
  · exact g32p_supplierForest_actual_019665
  · exact g32p_supplierForest_actual_019675
  · exact g32p_supplierForest_actual_019694
  · exact g32p_supplierForest_actual_019696
  · exact g32p_supplierForest_actual_019714
  · exact g32p_supplierForest_actual_019727
  · exact g32p_supplierForest_actual_019781
  · exact g32p_supplierForest_actual_019844
  · exact g32p_supplierForest_actual_019857
  · exact g32p_supplierForest_actual_019943
  · exact g32p_supplierForest_actual_019946
  · exact g32p_supplierForest_actual_019947
  · exact g32p_supplierForest_actual_020016
  · exact g32p_supplierForest_actual_020023
  · exact g32p_supplierForest_actual_020056
  · exact g32p_supplierForest_actual_020067
  · exact g32p_supplierForest_actual_020115
  · exact g32p_supplierForest_actual_020125
  · exact g32p_supplierForest_actual_020157
  · exact g32p_supplierForest_actual_020170
  · exact g32p_supplierForest_actual_020171
  · exact g32p_supplierForest_actual_020178
  · exact g32p_supplierForest_actual_020195
  · exact g32p_supplierForest_actual_020227
  · exact g32p_supplierForest_actual_020233
  · exact g32p_supplierForest_actual_020246
  · exact g32p_supplierForest_actual_020295
  · exact g32p_supplierForest_actual_020298
  · exact g32p_supplierForest_actual_020304
  · exact g32p_supplierForest_actual_020332
  · exact g32p_supplierForest_actual_020376
  · exact g32p_supplierForest_actual_020418
  · exact g32p_supplierForest_actual_020448
  · exact g32p_supplierForest_actual_020457
  · exact g32p_supplierForest_actual_020474
  · exact g32p_supplierForest_actual_020478
  · exact g32p_supplierForest_actual_020482
  · exact g32p_supplierForest_actual_020523
  · exact g32p_supplierForest_actual_020588
  · exact g32p_supplierForest_actual_020594
  · exact g32p_supplierForest_actual_020622
  · exact g32p_supplierForest_actual_020654
  · exact g32p_supplierForest_actual_020695
  · exact g32p_supplierForest_actual_020704
  · exact g32p_supplierForest_actual_020706
  · exact g32p_supplierForest_actual_020717
  · exact g32p_supplierForest_actual_020791
  · exact g32p_supplierForest_actual_020792
  · exact g32p_supplierForest_actual_020794
  · exact g32p_supplierForest_actual_020894
  · exact g32p_supplierForest_actual_020922
  · exact g32p_supplierForest_actual_020950
  · exact g32p_supplierForest_actual_020996
  · exact g32p_supplierForest_actual_021005
  · exact g32p_supplierForest_actual_021046
  · exact g32p_supplierForest_actual_021058
  · exact g32p_supplierForest_actual_021077
  · exact g32p_supplierForest_actual_021080
  · exact g32p_supplierForest_actual_021085
  · exact g32p_supplierForest_actual_021091
  · exact g32p_supplierForest_actual_021118
  · exact g32p_supplierForest_actual_021138
  · exact g32p_supplierForest_actual_021143
  · exact g32p_supplierForest_actual_021155
  · exact g32p_supplierForest_actual_021182
  · exact g32p_supplierForest_actual_021248
  · exact g32p_supplierForest_actual_021251
  · exact g32p_supplierForest_actual_021257
  · exact g32p_supplierForest_actual_021294
  · exact g32p_supplierForest_actual_021321
  · exact g32p_supplierForest_actual_021338
  · exact g32p_supplierForest_actual_021350
  · exact g32p_supplierForest_actual_021398
  · exact g32p_supplierForest_actual_021403
  · exact g32p_supplierForest_actual_021449
  · exact g32p_supplierForest_actual_021451
  · exact g32p_supplierForest_actual_021469
  · exact g32p_supplierForest_actual_021476
  · exact g32p_supplierForest_actual_021512
  · exact g32p_supplierForest_actual_021517
  · exact g32p_supplierForest_actual_021537
  · exact g32p_supplierForest_actual_021546
  · exact g32p_supplierForest_actual_021549
  · exact g32p_supplierForest_actual_021563
  · exact g32p_supplierForest_actual_021597
  · exact g32p_supplierForest_actual_021624
  · exact g32p_supplierForest_actual_021633

def g32p_supplierForest_nodes_018 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_021654 else g32p_supplierForest_node_021658) else (if i.val < 3 then g32p_supplierForest_node_021669 else g32p_supplierForest_node_021672)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_021673 else g32p_supplierForest_node_021727) else (if i.val < 7 then g32p_supplierForest_node_021810 else g32p_supplierForest_node_021831))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_021847 else g32p_supplierForest_node_021866) else (if i.val < 11 then g32p_supplierForest_node_021873 else g32p_supplierForest_node_021893)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_021917 else g32p_supplierForest_node_021924) else (if i.val < 15 then g32p_supplierForest_node_021943 else g32p_supplierForest_node_021953)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_021992 else g32p_supplierForest_node_022014) else (if i.val < 19 then g32p_supplierForest_node_022034 else g32p_supplierForest_node_022054)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_022073 else g32p_supplierForest_node_022078) else (if i.val < 23 then g32p_supplierForest_node_022100 else g32p_supplierForest_node_022162))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_022187 else g32p_supplierForest_node_022188) else (if i.val < 27 then g32p_supplierForest_node_022209 else g32p_supplierForest_node_022222)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_022224 else g32p_supplierForest_node_022262) else (if i.val < 31 then g32p_supplierForest_node_022267 else g32p_supplierForest_node_022288))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_022304 else g32p_supplierForest_node_022324) else (if i.val < 35 then g32p_supplierForest_node_022330 else g32p_supplierForest_node_022342)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_022348 else g32p_supplierForest_node_022351) else (if i.val < 39 then g32p_supplierForest_node_022399 else g32p_supplierForest_node_022413))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_022452 else g32p_supplierForest_node_022471) else (if i.val < 43 then g32p_supplierForest_node_022487 else g32p_supplierForest_node_022490)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_022567 else g32p_supplierForest_node_022576) else (if i.val < 47 then g32p_supplierForest_node_022579 else g32p_supplierForest_node_022580)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_022643 else g32p_supplierForest_node_022708) else (if i.val < 51 then g32p_supplierForest_node_022826 else g32p_supplierForest_node_022841)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_022998 else g32p_supplierForest_node_023016) else (if i.val < 55 then g32p_supplierForest_node_023042 else g32p_supplierForest_node_023206))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_023257 else g32p_supplierForest_node_023275) else (if i.val < 59 then g32p_supplierForest_node_023285 else g32p_supplierForest_node_023292)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_023303 else g32p_supplierForest_node_023325) else (if i.val < 63 then g32p_supplierForest_node_023328 else g32p_supplierForest_node_023354)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_023389 else g32p_supplierForest_node_023439) else (if i.val < 67 then g32p_supplierForest_node_023444 else g32p_supplierForest_node_023489)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_023547 else g32p_supplierForest_node_023586) else (if i.val < 71 then g32p_supplierForest_node_023648 else g32p_supplierForest_node_023677))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_023705 else g32p_supplierForest_node_023739) else (if i.val < 75 then g32p_supplierForest_node_023745 else g32p_supplierForest_node_023749)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_023763 else g32p_supplierForest_node_023795) else (if i.val < 79 then g32p_supplierForest_node_023867 else g32p_supplierForest_node_023873)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_023882 else g32p_supplierForest_node_023892) else (if i.val < 83 then g32p_supplierForest_node_023935 else g32p_supplierForest_node_024066)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_024075 else g32p_supplierForest_node_024179) else (if i.val < 87 then g32p_supplierForest_node_024216 else g32p_supplierForest_node_024229))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_024268 else g32p_supplierForest_node_024281) else (if i.val < 91 then g32p_supplierForest_node_024286 else g32p_supplierForest_node_024316)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_024321 else g32p_supplierForest_node_024333) else (if i.val < 95 then g32p_supplierForest_node_024377 else g32p_supplierForest_node_024387))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_024411 else g32p_supplierForest_node_024421) else (if i.val < 99 then g32p_supplierForest_node_024496 else g32p_supplierForest_node_024502)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_024503 else g32p_supplierForest_node_024538) else (if i.val < 103 then g32p_supplierForest_node_024573 else g32p_supplierForest_node_024576))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_024578 else g32p_supplierForest_node_024581) else (if i.val < 107 then g32p_supplierForest_node_024614 else g32p_supplierForest_node_024684)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_024753 else g32p_supplierForest_node_024763) else (if i.val < 111 then g32p_supplierForest_node_024766 else g32p_supplierForest_node_024770)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_024787 else g32p_supplierForest_node_024865) else (if i.val < 115 then g32p_supplierForest_node_024867 else g32p_supplierForest_node_024910)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_024945 else g32p_supplierForest_node_025008) else (if i.val < 119 then g32p_supplierForest_node_025056 else g32p_supplierForest_node_025062))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_025103 else g32p_supplierForest_node_025112) else (if i.val < 123 then g32p_supplierForest_node_025114 else g32p_supplierForest_node_025121)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_025123 else g32p_supplierForest_node_025132) else (if i.val < 127 then g32p_supplierForest_node_025142 else g32p_supplierForest_node_025184))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_025194 else g32p_supplierForest_node_025216) else (if i.val < 131 then g32p_supplierForest_node_025291 else g32p_supplierForest_node_025292)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_025334 else g32p_supplierForest_node_025377) else (if i.val < 135 then g32p_supplierForest_node_025389 else g32p_supplierForest_node_025393))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_025451 else g32p_supplierForest_node_025465) else (if i.val < 139 then g32p_supplierForest_node_025493 else g32p_supplierForest_node_025498)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_025500 else g32p_supplierForest_node_025529) else (if i.val < 143 then g32p_supplierForest_node_025546 else g32p_supplierForest_node_025575)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_025677 else g32p_supplierForest_node_025722) else (if i.val < 147 then g32p_supplierForest_node_025732 else g32p_supplierForest_node_025745)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_025775 else g32p_supplierForest_node_025813) else (if i.val < 151 then g32p_supplierForest_node_025822 else g32p_supplierForest_node_025845))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_025847 else g32p_supplierForest_node_025870) else (if i.val < 155 then g32p_supplierForest_node_025889 else g32p_supplierForest_node_025965)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_025999 else g32p_supplierForest_node_026000) else (if i.val < 159 then g32p_supplierForest_node_026006 else g32p_supplierForest_node_026031))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_026072 else g32p_supplierForest_node_026091) else (if i.val < 163 then g32p_supplierForest_node_026106 else g32p_supplierForest_node_026109)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_026115 else g32p_supplierForest_node_026131) else (if i.val < 167 then g32p_supplierForest_node_026205 else g32p_supplierForest_node_026235))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_026242 else g32p_supplierForest_node_026255) else (if i.val < 171 then g32p_supplierForest_node_026259 else g32p_supplierForest_node_026290)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_026298 else g32p_supplierForest_node_026301) else (if i.val < 175 then g32p_supplierForest_node_026302 else g32p_supplierForest_node_026327)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_026345 else g32p_supplierForest_node_026431) else (if i.val < 179 then g32p_supplierForest_node_026436 else g32p_supplierForest_node_026454)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_026460 else g32p_supplierForest_node_026550) else (if i.val < 183 then g32p_supplierForest_node_026556 else g32p_supplierForest_node_026584))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_026593 else g32p_supplierForest_node_026682) else (if i.val < 187 then g32p_supplierForest_node_026724 else g32p_supplierForest_node_026766)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_026767 else g32p_supplierForest_node_026771) else (if i.val < 191 then g32p_supplierForest_node_026775 else g32p_supplierForest_node_026830)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_026914 else g32p_supplierForest_node_026919) else (if i.val < 195 then g32p_supplierForest_node_026920 else g32p_supplierForest_node_026933)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_026992 else g32p_supplierForest_node_026997) else (if i.val < 199 then g32p_supplierForest_node_027009 else g32p_supplierForest_node_027053))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_027091 else g32p_supplierForest_node_027094) else (if i.val < 203 then g32p_supplierForest_node_027105 else g32p_supplierForest_node_027152)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_027183 else g32p_supplierForest_node_027252) else (if i.val < 207 then g32p_supplierForest_node_027264 else g32p_supplierForest_node_027281)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_027351 else g32p_supplierForest_node_027397) else (if i.val < 211 then g32p_supplierForest_node_027427 else g32p_supplierForest_node_027519)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_027526 else g32p_supplierForest_node_027573) else (if i.val < 215 then g32p_supplierForest_node_027666 else g32p_supplierForest_node_027675))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_027692 else g32p_supplierForest_node_027714) else (if i.val < 219 then g32p_supplierForest_node_027725 else g32p_supplierForest_node_027727)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_027775 else g32p_supplierForest_node_027781) else (if i.val < 223 then g32p_supplierForest_node_027801 else g32p_supplierForest_node_027826))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_027927 else g32p_supplierForest_node_027983) else (if i.val < 227 then g32p_supplierForest_node_028013 else g32p_supplierForest_node_028058)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_028062 else g32p_supplierForest_node_028090) else (if i.val < 231 then g32p_supplierForest_node_028094 else g32p_supplierForest_node_028096))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_028120 else g32p_supplierForest_node_028181) else (if i.val < 235 then g32p_supplierForest_node_028199 else g32p_supplierForest_node_028250)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_028254 else g32p_supplierForest_node_028271) else (if i.val < 239 then g32p_supplierForest_node_028290 else g32p_supplierForest_node_028300)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_028345 else g32p_supplierForest_node_028357) else (if i.val < 243 then g32p_supplierForest_node_028379 else g32p_supplierForest_node_028389)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_028392 else g32p_supplierForest_node_028396) else (if i.val < 247 then g32p_supplierForest_node_028450 else g32p_supplierForest_node_028472))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_028492 else g32p_supplierForest_node_028515) else (if i.val < 251 then g32p_supplierForest_node_028610 else g32p_supplierForest_node_028658)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_028671 else g32p_supplierForest_node_028688) else (if i.val < 255 then g32p_supplierForest_node_028692 else g32p_supplierForest_node_028709))))))))

def g32p_supplierForest_classes_018 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 47 else 48) else (if i.val < 3 then 13 else 50)) else (if i.val < 6 then (if i.val < 5 then 49 else 13) else (if i.val < 7 then 49 else 27))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 10 else 9) else (if i.val < 11 then 49 else 26)) else (if i.val < 14 then (if i.val < 13 then 27 else 27) else (if i.val < 15 then 26 else 8)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 48 else 49) else (if i.val < 19 then 51 else 13)) else (if i.val < 22 then (if i.val < 21 then 12 else 51) else (if i.val < 23 then 27 else 27))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 48 else 47) else (if i.val < 27 then 27 else 48)) else (if i.val < 30 then (if i.val < 29 then 47 else 51) else (if i.val < 31 then 10 else 49))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 48 else 10) else (if i.val < 35 then 25 else 49)) else (if i.val < 38 then (if i.val < 37 then 50 else 49) else (if i.val < 39 then 46 else 9))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 46 else 27) else (if i.val < 43 then 9 else 26)) else (if i.val < 46 then (if i.val < 45 then 9 else 12) else (if i.val < 47 then 49 else 12)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 46) else (if i.val < 51 then 46 else 8)) else (if i.val < 54 then (if i.val < 53 then 26 else 8) else (if i.val < 55 then 13 else 27))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 10 else 27) else (if i.val < 59 then 26 else 27)) else (if i.val < 62 then (if i.val < 61 then 26 else 25) else (if i.val < 63 then 48 else 13)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 9) else (if i.val < 67 then 12 else 25)) else (if i.val < 70 then (if i.val < 69 then 47 else 49) else (if i.val < 71 then 27 else 47))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 12 else 48) else (if i.val < 75 then 47 else 52)) else (if i.val < 78 then (if i.val < 77 then 48 else 50) else (if i.val < 79 then 50 else 12)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 25 else 51) else (if i.val < 83 then 51 else 47)) else (if i.val < 86 then (if i.val < 85 then 9 else 10) else (if i.val < 87 then 11 else 8))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 13 else 26) else (if i.val < 91 then 27 else 46)) else (if i.val < 94 then (if i.val < 93 then 12 else 47) else (if i.val < 95 then 26 else 26))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 27 else 13) else (if i.val < 99 then 4 else 29)) else (if i.val < 102 then (if i.val < 101 then 16 else 15) else (if i.val < 103 then 15 else 4))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 30 else 32) else (if i.val < 107 then 30 else 57)) else (if i.val < 110 then (if i.val < 109 then 31 else 29) else (if i.val < 111 then 30 else 32)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 16 else 32) else (if i.val < 115 then 4 else 30)) else (if i.val < 118 then (if i.val < 117 then 3 else 17) else (if i.val < 119 then 34 else 60))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 3 else 17) else (if i.val < 123 then 15 else 15)) else (if i.val < 126 then (if i.val < 125 then 15 else 34) else (if i.val < 127 then 14 else 57))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 29 else 58) else (if i.val < 131 then 57 else 59)) else (if i.val < 134 then (if i.val < 133 then 59 else 30) else (if i.val < 135 then 30 else 30))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 29 else 33) else (if i.val < 139 then 17 else 16)) else (if i.val < 142 then (if i.val < 141 then 14 else 14) else (if i.val < 143 then 15 else 17)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 15 else 4) else (if i.val < 147 then 32 else 36)) else (if i.val < 150 then (if i.val < 149 then 14 else 36) else (if i.val < 151 then 30 else 30))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 14 else 32) else (if i.val < 155 then 16 else 30)) else (if i.val < 158 then (if i.val < 157 then 30 else 33) else (if i.val < 159 then 16 else 34))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 17 else 36) else (if i.val < 163 then 14 else 16)) else (if i.val < 166 then (if i.val < 165 then 63 else 15) else (if i.val < 167 then 61 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 59 else 60) else (if i.val < 171 then 62 else 57)) else (if i.val < 174 then (if i.val < 173 then 31 else 31) else (if i.val < 175 then 30 else 17)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 4 else 57) else (if i.val < 179 then 58 else 57)) else (if i.val < 182 then (if i.val < 181 then 57 else 57) else (if i.val < 183 then 17 else 30))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 63 else 34) else (if i.val < 187 then 16 else 64)) else (if i.val < 190 then (if i.val < 189 then 57 else 32) else (if i.val < 191 then 63 else 32)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 15 else 57) else (if i.val < 195 then 65 else 58)) else (if i.val < 198 then (if i.val < 197 then 57 else 17) else (if i.val < 199 then 15 else 34))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 34 else 33) else (if i.val < 203 then 58 else 3)) else (if i.val < 206 then (if i.val < 205 then 4 else 32) else (if i.val < 207 then 17 else 4)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 36 else 32) else (if i.val < 211 then 57 else 30)) else (if i.val < 214 then (if i.val < 213 then 34 else 14) else (if i.val < 215 then 14 else 16))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 15 else 17) else (if i.val < 219 then 31 else 30)) else (if i.val < 222 then (if i.val < 221 then 32 else 4) else (if i.val < 223 then 34 else 36))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 32 else 17) else (if i.val < 227 then 34 else 15)) else (if i.val < 230 then (if i.val < 229 then 14 else 17) else (if i.val < 231 then 34 else 15))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 15 else 14) else (if i.val < 235 then 17 else 16)) else (if i.val < 238 then (if i.val < 237 then 16 else 15) else (if i.val < 239 then 33 else 36)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 4 else 57) else (if i.val < 243 then 34 else 31)) else (if i.val < 246 then (if i.val < 245 then 16 else 14) else (if i.val < 247 then 59 else 36))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 57 else 34) else (if i.val < 251 then 32 else 32)) else (if i.val < 254 then (if i.val < 253 then 34 else 59) else (if i.val < 255 then 31 else 15))))))))

theorem g32p_supplierForest_actual_018 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_018 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_018 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_021654
  · exact g32p_supplierForest_actual_021658
  · exact g32p_supplierForest_actual_021669
  · exact g32p_supplierForest_actual_021672
  · exact g32p_supplierForest_actual_021673
  · exact g32p_supplierForest_actual_021727
  · exact g32p_supplierForest_actual_021810
  · exact g32p_supplierForest_actual_021831
  · exact g32p_supplierForest_actual_021847
  · exact g32p_supplierForest_actual_021866
  · exact g32p_supplierForest_actual_021873
  · exact g32p_supplierForest_actual_021893
  · exact g32p_supplierForest_actual_021917
  · exact g32p_supplierForest_actual_021924
  · exact g32p_supplierForest_actual_021943
  · exact g32p_supplierForest_actual_021953
  · exact g32p_supplierForest_actual_021992
  · exact g32p_supplierForest_actual_022014
  · exact g32p_supplierForest_actual_022034
  · exact g32p_supplierForest_actual_022054
  · exact g32p_supplierForest_actual_022073
  · exact g32p_supplierForest_actual_022078
  · exact g32p_supplierForest_actual_022100
  · exact g32p_supplierForest_actual_022162
  · exact g32p_supplierForest_actual_022187
  · exact g32p_supplierForest_actual_022188
  · exact g32p_supplierForest_actual_022209
  · exact g32p_supplierForest_actual_022222
  · exact g32p_supplierForest_actual_022224
  · exact g32p_supplierForest_actual_022262
  · exact g32p_supplierForest_actual_022267
  · exact g32p_supplierForest_actual_022288
  · exact g32p_supplierForest_actual_022304
  · exact g32p_supplierForest_actual_022324
  · exact g32p_supplierForest_actual_022330
  · exact g32p_supplierForest_actual_022342
  · exact g32p_supplierForest_actual_022348
  · exact g32p_supplierForest_actual_022351
  · exact g32p_supplierForest_actual_022399
  · exact g32p_supplierForest_actual_022413
  · exact g32p_supplierForest_actual_022452
  · exact g32p_supplierForest_actual_022471
  · exact g32p_supplierForest_actual_022487
  · exact g32p_supplierForest_actual_022490
  · exact g32p_supplierForest_actual_022567
  · exact g32p_supplierForest_actual_022576
  · exact g32p_supplierForest_actual_022579
  · exact g32p_supplierForest_actual_022580
  · exact g32p_supplierForest_actual_022643
  · exact g32p_supplierForest_actual_022708
  · exact g32p_supplierForest_actual_022826
  · exact g32p_supplierForest_actual_022841
  · exact g32p_supplierForest_actual_022998
  · exact g32p_supplierForest_actual_023016
  · exact g32p_supplierForest_actual_023042
  · exact g32p_supplierForest_actual_023206
  · exact g32p_supplierForest_actual_023257
  · exact g32p_supplierForest_actual_023275
  · exact g32p_supplierForest_actual_023285
  · exact g32p_supplierForest_actual_023292
  · exact g32p_supplierForest_actual_023303
  · exact g32p_supplierForest_actual_023325
  · exact g32p_supplierForest_actual_023328
  · exact g32p_supplierForest_actual_023354
  · exact g32p_supplierForest_actual_023389
  · exact g32p_supplierForest_actual_023439
  · exact g32p_supplierForest_actual_023444
  · exact g32p_supplierForest_actual_023489
  · exact g32p_supplierForest_actual_023547
  · exact g32p_supplierForest_actual_023586
  · exact g32p_supplierForest_actual_023648
  · exact g32p_supplierForest_actual_023677
  · exact g32p_supplierForest_actual_023705
  · exact g32p_supplierForest_actual_023739
  · exact g32p_supplierForest_actual_023745
  · exact g32p_supplierForest_actual_023749
  · exact g32p_supplierForest_actual_023763
  · exact g32p_supplierForest_actual_023795
  · exact g32p_supplierForest_actual_023867
  · exact g32p_supplierForest_actual_023873
  · exact g32p_supplierForest_actual_023882
  · exact g32p_supplierForest_actual_023892
  · exact g32p_supplierForest_actual_023935
  · exact g32p_supplierForest_actual_024066
  · exact g32p_supplierForest_actual_024075
  · exact g32p_supplierForest_actual_024179
  · exact g32p_supplierForest_actual_024216
  · exact g32p_supplierForest_actual_024229
  · exact g32p_supplierForest_actual_024268
  · exact g32p_supplierForest_actual_024281
  · exact g32p_supplierForest_actual_024286
  · exact g32p_supplierForest_actual_024316
  · exact g32p_supplierForest_actual_024321
  · exact g32p_supplierForest_actual_024333
  · exact g32p_supplierForest_actual_024377
  · exact g32p_supplierForest_actual_024387
  · exact g32p_supplierForest_actual_024411
  · exact g32p_supplierForest_actual_024421
  · exact g32p_supplierForest_actual_024496
  · exact g32p_supplierForest_actual_024502
  · exact g32p_supplierForest_actual_024503
  · exact g32p_supplierForest_actual_024538
  · exact g32p_supplierForest_actual_024573
  · exact g32p_supplierForest_actual_024576
  · exact g32p_supplierForest_actual_024578
  · exact g32p_supplierForest_actual_024581
  · exact g32p_supplierForest_actual_024614
  · exact g32p_supplierForest_actual_024684
  · exact g32p_supplierForest_actual_024753
  · exact g32p_supplierForest_actual_024763
  · exact g32p_supplierForest_actual_024766
  · exact g32p_supplierForest_actual_024770
  · exact g32p_supplierForest_actual_024787
  · exact g32p_supplierForest_actual_024865
  · exact g32p_supplierForest_actual_024867
  · exact g32p_supplierForest_actual_024910
  · exact g32p_supplierForest_actual_024945
  · exact g32p_supplierForest_actual_025008
  · exact g32p_supplierForest_actual_025056
  · exact g32p_supplierForest_actual_025062
  · exact g32p_supplierForest_actual_025103
  · exact g32p_supplierForest_actual_025112
  · exact g32p_supplierForest_actual_025114
  · exact g32p_supplierForest_actual_025121
  · exact g32p_supplierForest_actual_025123
  · exact g32p_supplierForest_actual_025132
  · exact g32p_supplierForest_actual_025142
  · exact g32p_supplierForest_actual_025184
  · exact g32p_supplierForest_actual_025194
  · exact g32p_supplierForest_actual_025216
  · exact g32p_supplierForest_actual_025291
  · exact g32p_supplierForest_actual_025292
  · exact g32p_supplierForest_actual_025334
  · exact g32p_supplierForest_actual_025377
  · exact g32p_supplierForest_actual_025389
  · exact g32p_supplierForest_actual_025393
  · exact g32p_supplierForest_actual_025451
  · exact g32p_supplierForest_actual_025465
  · exact g32p_supplierForest_actual_025493
  · exact g32p_supplierForest_actual_025498
  · exact g32p_supplierForest_actual_025500
  · exact g32p_supplierForest_actual_025529
  · exact g32p_supplierForest_actual_025546
  · exact g32p_supplierForest_actual_025575
  · exact g32p_supplierForest_actual_025677
  · exact g32p_supplierForest_actual_025722
  · exact g32p_supplierForest_actual_025732
  · exact g32p_supplierForest_actual_025745
  · exact g32p_supplierForest_actual_025775
  · exact g32p_supplierForest_actual_025813
  · exact g32p_supplierForest_actual_025822
  · exact g32p_supplierForest_actual_025845
  · exact g32p_supplierForest_actual_025847
  · exact g32p_supplierForest_actual_025870
  · exact g32p_supplierForest_actual_025889
  · exact g32p_supplierForest_actual_025965
  · exact g32p_supplierForest_actual_025999
  · exact g32p_supplierForest_actual_026000
  · exact g32p_supplierForest_actual_026006
  · exact g32p_supplierForest_actual_026031
  · exact g32p_supplierForest_actual_026072
  · exact g32p_supplierForest_actual_026091
  · exact g32p_supplierForest_actual_026106
  · exact g32p_supplierForest_actual_026109
  · exact g32p_supplierForest_actual_026115
  · exact g32p_supplierForest_actual_026131
  · exact g32p_supplierForest_actual_026205
  · exact g32p_supplierForest_actual_026235
  · exact g32p_supplierForest_actual_026242
  · exact g32p_supplierForest_actual_026255
  · exact g32p_supplierForest_actual_026259
  · exact g32p_supplierForest_actual_026290
  · exact g32p_supplierForest_actual_026298
  · exact g32p_supplierForest_actual_026301
  · exact g32p_supplierForest_actual_026302
  · exact g32p_supplierForest_actual_026327
  · exact g32p_supplierForest_actual_026345
  · exact g32p_supplierForest_actual_026431
  · exact g32p_supplierForest_actual_026436
  · exact g32p_supplierForest_actual_026454
  · exact g32p_supplierForest_actual_026460
  · exact g32p_supplierForest_actual_026550
  · exact g32p_supplierForest_actual_026556
  · exact g32p_supplierForest_actual_026584
  · exact g32p_supplierForest_actual_026593
  · exact g32p_supplierForest_actual_026682
  · exact g32p_supplierForest_actual_026724
  · exact g32p_supplierForest_actual_026766
  · exact g32p_supplierForest_actual_026767
  · exact g32p_supplierForest_actual_026771
  · exact g32p_supplierForest_actual_026775
  · exact g32p_supplierForest_actual_026830
  · exact g32p_supplierForest_actual_026914
  · exact g32p_supplierForest_actual_026919
  · exact g32p_supplierForest_actual_026920
  · exact g32p_supplierForest_actual_026933
  · exact g32p_supplierForest_actual_026992
  · exact g32p_supplierForest_actual_026997
  · exact g32p_supplierForest_actual_027009
  · exact g32p_supplierForest_actual_027053
  · exact g32p_supplierForest_actual_027091
  · exact g32p_supplierForest_actual_027094
  · exact g32p_supplierForest_actual_027105
  · exact g32p_supplierForest_actual_027152
  · exact g32p_supplierForest_actual_027183
  · exact g32p_supplierForest_actual_027252
  · exact g32p_supplierForest_actual_027264
  · exact g32p_supplierForest_actual_027281
  · exact g32p_supplierForest_actual_027351
  · exact g32p_supplierForest_actual_027397
  · exact g32p_supplierForest_actual_027427
  · exact g32p_supplierForest_actual_027519
  · exact g32p_supplierForest_actual_027526
  · exact g32p_supplierForest_actual_027573
  · exact g32p_supplierForest_actual_027666
  · exact g32p_supplierForest_actual_027675
  · exact g32p_supplierForest_actual_027692
  · exact g32p_supplierForest_actual_027714
  · exact g32p_supplierForest_actual_027725
  · exact g32p_supplierForest_actual_027727
  · exact g32p_supplierForest_actual_027775
  · exact g32p_supplierForest_actual_027781
  · exact g32p_supplierForest_actual_027801
  · exact g32p_supplierForest_actual_027826
  · exact g32p_supplierForest_actual_027927
  · exact g32p_supplierForest_actual_027983
  · exact g32p_supplierForest_actual_028013
  · exact g32p_supplierForest_actual_028058
  · exact g32p_supplierForest_actual_028062
  · exact g32p_supplierForest_actual_028090
  · exact g32p_supplierForest_actual_028094
  · exact g32p_supplierForest_actual_028096
  · exact g32p_supplierForest_actual_028120
  · exact g32p_supplierForest_actual_028181
  · exact g32p_supplierForest_actual_028199
  · exact g32p_supplierForest_actual_028250
  · exact g32p_supplierForest_actual_028254
  · exact g32p_supplierForest_actual_028271
  · exact g32p_supplierForest_actual_028290
  · exact g32p_supplierForest_actual_028300
  · exact g32p_supplierForest_actual_028345
  · exact g32p_supplierForest_actual_028357
  · exact g32p_supplierForest_actual_028379
  · exact g32p_supplierForest_actual_028389
  · exact g32p_supplierForest_actual_028392
  · exact g32p_supplierForest_actual_028396
  · exact g32p_supplierForest_actual_028450
  · exact g32p_supplierForest_actual_028472
  · exact g32p_supplierForest_actual_028492
  · exact g32p_supplierForest_actual_028515
  · exact g32p_supplierForest_actual_028610
  · exact g32p_supplierForest_actual_028658
  · exact g32p_supplierForest_actual_028671
  · exact g32p_supplierForest_actual_028688
  · exact g32p_supplierForest_actual_028692
  · exact g32p_supplierForest_actual_028709

def g32p_supplierForest_nodes_019 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_028757 else g32p_supplierForest_node_028760) else (if i.val < 3 then g32p_supplierForest_node_028767 else g32p_supplierForest_node_028768)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_028772 else g32p_supplierForest_node_028809) else (if i.val < 7 then g32p_supplierForest_node_028814 else g32p_supplierForest_node_028841))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_028849 else g32p_supplierForest_node_028863) else (if i.val < 11 then g32p_supplierForest_node_028873 else g32p_supplierForest_node_028898)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_028936 else g32p_supplierForest_node_029001) else (if i.val < 15 then g32p_supplierForest_node_029025 else g32p_supplierForest_node_029029)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_029032 else g32p_supplierForest_node_029065) else (if i.val < 19 then g32p_supplierForest_node_029073 else g32p_supplierForest_node_029096)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_029104 else g32p_supplierForest_node_029216) else (if i.val < 23 then g32p_supplierForest_node_029227 else g32p_supplierForest_node_029239))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_029303 else g32p_supplierForest_node_029307) else (if i.val < 27 then g32p_supplierForest_node_029318 else g32p_supplierForest_node_029323)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_029375 else g32p_supplierForest_node_029387) else (if i.val < 31 then g32p_supplierForest_node_029392 else g32p_supplierForest_node_029396))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_029399 else g32p_supplierForest_node_029404) else (if i.val < 35 then g32p_supplierForest_node_029414 else g32p_supplierForest_node_029461)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_029464 else g32p_supplierForest_node_029485) else (if i.val < 39 then g32p_supplierForest_node_029486 else g32p_supplierForest_node_029491))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_029504 else g32p_supplierForest_node_029507) else (if i.val < 43 then g32p_supplierForest_node_029533 else g32p_supplierForest_node_029550)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_029560 else g32p_supplierForest_node_029587) else (if i.val < 47 then g32p_supplierForest_node_029593 else g32p_supplierForest_node_029630)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_029650 else g32p_supplierForest_node_029704) else (if i.val < 51 then g32p_supplierForest_node_029746 else g32p_supplierForest_node_029751)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_029785 else g32p_supplierForest_node_029787) else (if i.val < 55 then g32p_supplierForest_node_029797 else g32p_supplierForest_node_029818))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_029820 else g32p_supplierForest_node_029844) else (if i.val < 59 then g32p_supplierForest_node_029847 else g32p_supplierForest_node_029849)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_029859 else g32p_supplierForest_node_029867) else (if i.val < 63 then g32p_supplierForest_node_029889 else g32p_supplierForest_node_029897)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_029916 else g32p_supplierForest_node_030001) else (if i.val < 67 then g32p_supplierForest_node_030010 else g32p_supplierForest_node_030012)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_030032 else g32p_supplierForest_node_030034) else (if i.val < 71 then g32p_supplierForest_node_030054 else g32p_supplierForest_node_030063))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_030081 else g32p_supplierForest_node_030089) else (if i.val < 75 then g32p_supplierForest_node_030109 else g32p_supplierForest_node_030111)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_030117 else g32p_supplierForest_node_030160) else (if i.val < 79 then g32p_supplierForest_node_030179 else g32p_supplierForest_node_030226)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_030245 else g32p_supplierForest_node_030249) else (if i.val < 83 then g32p_supplierForest_node_030259 else g32p_supplierForest_node_030287)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_030317 else g32p_supplierForest_node_030394) else (if i.val < 87 then g32p_supplierForest_node_030403 else g32p_supplierForest_node_030419))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_030420 else g32p_supplierForest_node_030458) else (if i.val < 91 then g32p_supplierForest_node_030486 else g32p_supplierForest_node_030488)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_030499 else g32p_supplierForest_node_030543) else (if i.val < 95 then g32p_supplierForest_node_030562 else g32p_supplierForest_node_030583))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_030602 else g32p_supplierForest_node_030700) else (if i.val < 99 then g32p_supplierForest_node_030734 else g32p_supplierForest_node_030737)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_030792 else g32p_supplierForest_node_030800) else (if i.val < 103 then g32p_supplierForest_node_030822 else g32p_supplierForest_node_030837))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_030850 else g32p_supplierForest_node_030932) else (if i.val < 107 then g32p_supplierForest_node_030968 else g32p_supplierForest_node_031031)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_031046 else g32p_supplierForest_node_031052) else (if i.val < 111 then g32p_supplierForest_node_031082 else g32p_supplierForest_node_031087)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_031109 else g32p_supplierForest_node_031123) else (if i.val < 115 then g32p_supplierForest_node_031125 else g32p_supplierForest_node_031129)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_031134 else g32p_supplierForest_node_031175) else (if i.val < 119 then g32p_supplierForest_node_031209 else g32p_supplierForest_node_031247))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_031257 else g32p_supplierForest_node_031362) else (if i.val < 123 then g32p_supplierForest_node_031390 else g32p_supplierForest_node_031458)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_031491 else g32p_supplierForest_node_031531) else (if i.val < 127 then g32p_supplierForest_node_031597 else g32p_supplierForest_node_031656))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_031757 else g32p_supplierForest_node_031759) else (if i.val < 131 then g32p_supplierForest_node_031790 else g32p_supplierForest_node_031802)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_031810 else g32p_supplierForest_node_031821) else (if i.val < 135 then g32p_supplierForest_node_031923 else g32p_supplierForest_node_031926))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_031979 else g32p_supplierForest_node_032086) else (if i.val < 139 then g32p_supplierForest_node_032094 else g32p_supplierForest_node_032107)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_032112 else g32p_supplierForest_node_032113) else (if i.val < 143 then g32p_supplierForest_node_032132 else g32p_supplierForest_node_032172)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_032176 else g32p_supplierForest_node_032251) else (if i.val < 147 then g32p_supplierForest_node_032330 else g32p_supplierForest_node_032373)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_032441 else g32p_supplierForest_node_032445) else (if i.val < 151 then g32p_supplierForest_node_032470 else g32p_supplierForest_node_032478))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_032518 else g32p_supplierForest_node_032526) else (if i.val < 155 then g32p_supplierForest_node_032621 else g32p_supplierForest_node_032631)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_032672 else g32p_supplierForest_node_032692) else (if i.val < 159 then g32p_supplierForest_node_032699 else g32p_supplierForest_node_032734))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_032806 else g32p_supplierForest_node_032808) else (if i.val < 163 then g32p_supplierForest_node_032853 else g32p_supplierForest_node_032896)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_032975 else g32p_supplierForest_node_033009) else (if i.val < 167 then g32p_supplierForest_node_033025 else g32p_supplierForest_node_033122))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_033179 else g32p_supplierForest_node_033201) else (if i.val < 171 then g32p_supplierForest_node_033303 else g32p_supplierForest_node_033308)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_033406 else g32p_supplierForest_node_033438) else (if i.val < 175 then g32p_supplierForest_node_033486 else g32p_supplierForest_node_033520)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_033541 else g32p_supplierForest_node_033549) else (if i.val < 179 then g32p_supplierForest_node_033579 else g32p_supplierForest_node_033690)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_033721 else g32p_supplierForest_node_033742) else (if i.val < 183 then g32p_supplierForest_node_033812 else g32p_supplierForest_node_033855))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_033863 else g32p_supplierForest_node_033945) else (if i.val < 187 then g32p_supplierForest_node_033979 else g32p_supplierForest_node_034005)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_034033 else g32p_supplierForest_node_034131) else (if i.val < 191 then g32p_supplierForest_node_034197 else g32p_supplierForest_node_034299)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_034330 else g32p_supplierForest_node_034380) else (if i.val < 195 then g32p_supplierForest_node_034414 else g32p_supplierForest_node_034475)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_034484 else g32p_supplierForest_node_034498) else (if i.val < 199 then g32p_supplierForest_node_034536 else g32p_supplierForest_node_034554))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_034589 else g32p_supplierForest_node_034628) else (if i.val < 203 then g32p_supplierForest_node_034664 else g32p_supplierForest_node_034760)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_034764 else g32p_supplierForest_node_034769) else (if i.val < 207 then g32p_supplierForest_node_034800 else g32p_supplierForest_node_034825)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_034829 else g32p_supplierForest_node_034863) else (if i.val < 211 then g32p_supplierForest_node_035002 else g32p_supplierForest_node_035072)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_035157 else g32p_supplierForest_node_035167) else (if i.val < 215 then g32p_supplierForest_node_035171 else g32p_supplierForest_node_035183))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_035208 else g32p_supplierForest_node_035213) else (if i.val < 219 then g32p_supplierForest_node_035241 else g32p_supplierForest_node_035246)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_035303 else g32p_supplierForest_node_035316) else (if i.val < 223 then g32p_supplierForest_node_035344 else g32p_supplierForest_node_035346))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_035376 else g32p_supplierForest_node_035403) else (if i.val < 227 then g32p_supplierForest_node_035442 else g32p_supplierForest_node_035511)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_035524 else g32p_supplierForest_node_035526) else (if i.val < 231 then g32p_supplierForest_node_035679 else g32p_supplierForest_node_035683))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_035703 else g32p_supplierForest_node_035705) else (if i.val < 235 then g32p_supplierForest_node_035714 else g32p_supplierForest_node_035717)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_035735 else g32p_supplierForest_node_035743) else (if i.val < 239 then g32p_supplierForest_node_035787 else g32p_supplierForest_node_035791)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_035832 else g32p_supplierForest_node_035962) else (if i.val < 243 then g32p_supplierForest_node_035976 else g32p_supplierForest_node_036033)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_036052 else g32p_supplierForest_node_036077) else (if i.val < 247 then g32p_supplierForest_node_036131 else g32p_supplierForest_node_036145))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_036184 else g32p_supplierForest_node_036226) else (if i.val < 251 then g32p_supplierForest_node_036467 else g32p_supplierForest_node_036468)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_036504 else g32p_supplierForest_node_036505) else (if i.val < 255 then g32p_supplierForest_node_036559 else g32p_supplierForest_node_036646))))))))

def g32p_supplierForest_classes_019 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 30 else 57) else (if i.val < 3 then 59 else 57)) else (if i.val < 6 then (if i.val < 5 then 31 else 59) else (if i.val < 7 then 58 else 60))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 59 else 58) else (if i.val < 11 then 61 else 32)) else (if i.val < 14 then (if i.val < 13 then 31 else 63) else (if i.val < 15 then 32 else 58)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 59 else 17) else (if i.val < 19 then 57 else 64)) else (if i.val < 22 then (if i.val < 21 then 16 else 65) else (if i.val < 23 then 61 else 32))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 60 else 57) else (if i.val < 27 then 57 else 57)) else (if i.val < 30 then (if i.val < 29 then 29 else 16) else (if i.val < 31 then 57 else 15))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 15 else 15) else (if i.val < 35 then 58 else 57)) else (if i.val < 38 then (if i.val < 37 then 17 else 34) else (if i.val < 39 then 33 else 57))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 57 else 34) else (if i.val < 43 then 30 else 16)) else (if i.val < 46 then (if i.val < 45 then 59 else 60) else (if i.val < 47 then 34 else 30)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 17 else 16) else (if i.val < 51 then 61 else 62)) else (if i.val < 54 then (if i.val < 53 then 59 else 30) else (if i.val < 55 then 60 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 31 else 30) else (if i.val < 59 then 17 else 29)) else (if i.val < 62 then (if i.val < 61 then 16 else 57) else (if i.val < 63 then 31 else 36)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 30 else 33) else (if i.val < 67 then 31 else 14)) else (if i.val < 70 then (if i.val < 69 then 3 else 14) else (if i.val < 71 then 2 else 16))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 30 else 36) else (if i.val < 75 then 63 else 65)) else (if i.val < 78 then (if i.val < 77 then 14 else 14) else (if i.val < 79 then 16 else 34)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 31 else 32) else (if i.val < 83 then 57 else 63)) else (if i.val < 86 then (if i.val < 85 then 64 else 59) else (if i.val < 87 then 15 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 60 else 33) else (if i.val < 91 then 57 else 63)) else (if i.val < 94 then (if i.val < 93 then 32 else 32) else (if i.val < 95 then 61 else 4))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 63 else 63) else (if i.val < 99 then 32 else 16)) else (if i.val < 102 then (if i.val < 101 then 63 else 16) else (if i.val < 103 then 34 else 32))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 35 else 4) else (if i.val < 107 then 32 else 15)) else (if i.val < 110 then (if i.val < 109 then 16 else 30) else (if i.val < 111 then 65 else 16)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 36 else 30) else (if i.val < 115 then 36 else 16)) else (if i.val < 118 then (if i.val < 117 then 36 else 64) else (if i.val < 119 then 4 else 15))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 58 else 34) else (if i.val < 123 then 65 else 30)) else (if i.val < 126 then (if i.val < 125 then 16 else 65) else (if i.val < 127 then 57 else 31))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 57 else 34) else (if i.val < 131 then 57 else 17)) else (if i.val < 134 then (if i.val < 133 then 65 else 4) else (if i.val < 135 then 58 else 60))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 32 else 58) else (if i.val < 139 then 14 else 17)) else (if i.val < 142 then (if i.val < 141 then 57 else 59) else (if i.val < 143 then 60 else 59)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 57 else 29) else (if i.val < 147 then 63 else 33)) else (if i.val < 150 then (if i.val < 149 then 16 else 66) else (if i.val < 151 then 30 else 57))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 63 else 63) else (if i.val < 155 then 57 else 30)) else (if i.val < 158 then (if i.val < 157 then 32 else 62) else (if i.val < 159 then 60 else 59))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 57 else 35) else (if i.val < 163 then 16 else 57)) else (if i.val < 166 then (if i.val < 165 then 4 else 32) else (if i.val < 167 then 4 else 15))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 32 else 16) else (if i.val < 171 then 36 else 16)) else (if i.val < 174 then (if i.val < 173 then 32 else 32) else (if i.val < 175 then 17 else 17)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 57 else 62) else (if i.val < 179 then 30 else 34)) else (if i.val < 182 then (if i.val < 181 then 34 else 32) else (if i.val < 183 then 33 else 34))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 16 else 64) else (if i.val < 187 then 32 else 15)) else (if i.val < 190 then (if i.val < 189 then 66 else 59) else (if i.val < 191 then 32 else 15)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 36 else 57) else (if i.val < 195 then 34 else 35)) else (if i.val < 198 then (if i.val < 197 then 34 else 16) else (if i.val < 199 then 15 else 62))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 17 else 60) else (if i.val < 203 then 34 else 29)) else (if i.val < 206 then (if i.val < 205 then 57 else 57) else (if i.val < 207 then 16 else 15)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 60 else 30) else (if i.val < 211 then 57 else 58)) else (if i.val < 214 then (if i.val < 213 then 65 else 57) else (if i.val < 215 then 59 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 59 else 15) else (if i.val < 219 then 30 else 57)) else (if i.val < 222 then (if i.val < 221 then 36 else 32) else (if i.val < 223 then 3 else 15))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 34 else 31) else (if i.val < 227 then 57 else 15)) else (if i.val < 230 then (if i.val < 229 then 57 else 57) else (if i.val < 231 then 65 else 64))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 64 else 65) else (if i.val < 235 then 59 else 34)) else (if i.val < 238 then (if i.val < 237 then 64 else 64) else (if i.val < 239 then 33 else 60)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 31 else 16) else (if i.val < 243 then 36 else 63)) else (if i.val < 246 then (if i.val < 245 then 60 else 33) else (if i.val < 247 then 16 else 36))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 64 else 36) else (if i.val < 251 then 15 else 34)) else (if i.val < 254 then (if i.val < 253 then 32 else 35) else (if i.val < 255 then 34 else 3))))))))

theorem g32p_supplierForest_actual_019 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_019 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_019 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_028757
  · exact g32p_supplierForest_actual_028760
  · exact g32p_supplierForest_actual_028767
  · exact g32p_supplierForest_actual_028768
  · exact g32p_supplierForest_actual_028772
  · exact g32p_supplierForest_actual_028809
  · exact g32p_supplierForest_actual_028814
  · exact g32p_supplierForest_actual_028841
  · exact g32p_supplierForest_actual_028849
  · exact g32p_supplierForest_actual_028863
  · exact g32p_supplierForest_actual_028873
  · exact g32p_supplierForest_actual_028898
  · exact g32p_supplierForest_actual_028936
  · exact g32p_supplierForest_actual_029001
  · exact g32p_supplierForest_actual_029025
  · exact g32p_supplierForest_actual_029029
  · exact g32p_supplierForest_actual_029032
  · exact g32p_supplierForest_actual_029065
  · exact g32p_supplierForest_actual_029073
  · exact g32p_supplierForest_actual_029096
  · exact g32p_supplierForest_actual_029104
  · exact g32p_supplierForest_actual_029216
  · exact g32p_supplierForest_actual_029227
  · exact g32p_supplierForest_actual_029239
  · exact g32p_supplierForest_actual_029303
  · exact g32p_supplierForest_actual_029307
  · exact g32p_supplierForest_actual_029318
  · exact g32p_supplierForest_actual_029323
  · exact g32p_supplierForest_actual_029375
  · exact g32p_supplierForest_actual_029387
  · exact g32p_supplierForest_actual_029392
  · exact g32p_supplierForest_actual_029396
  · exact g32p_supplierForest_actual_029399
  · exact g32p_supplierForest_actual_029404
  · exact g32p_supplierForest_actual_029414
  · exact g32p_supplierForest_actual_029461
  · exact g32p_supplierForest_actual_029464
  · exact g32p_supplierForest_actual_029485
  · exact g32p_supplierForest_actual_029486
  · exact g32p_supplierForest_actual_029491
  · exact g32p_supplierForest_actual_029504
  · exact g32p_supplierForest_actual_029507
  · exact g32p_supplierForest_actual_029533
  · exact g32p_supplierForest_actual_029550
  · exact g32p_supplierForest_actual_029560
  · exact g32p_supplierForest_actual_029587
  · exact g32p_supplierForest_actual_029593
  · exact g32p_supplierForest_actual_029630
  · exact g32p_supplierForest_actual_029650
  · exact g32p_supplierForest_actual_029704
  · exact g32p_supplierForest_actual_029746
  · exact g32p_supplierForest_actual_029751
  · exact g32p_supplierForest_actual_029785
  · exact g32p_supplierForest_actual_029787
  · exact g32p_supplierForest_actual_029797
  · exact g32p_supplierForest_actual_029818
  · exact g32p_supplierForest_actual_029820
  · exact g32p_supplierForest_actual_029844
  · exact g32p_supplierForest_actual_029847
  · exact g32p_supplierForest_actual_029849
  · exact g32p_supplierForest_actual_029859
  · exact g32p_supplierForest_actual_029867
  · exact g32p_supplierForest_actual_029889
  · exact g32p_supplierForest_actual_029897
  · exact g32p_supplierForest_actual_029916
  · exact g32p_supplierForest_actual_030001
  · exact g32p_supplierForest_actual_030010
  · exact g32p_supplierForest_actual_030012
  · exact g32p_supplierForest_actual_030032
  · exact g32p_supplierForest_actual_030034
  · exact g32p_supplierForest_actual_030054
  · exact g32p_supplierForest_actual_030063
  · exact g32p_supplierForest_actual_030081
  · exact g32p_supplierForest_actual_030089
  · exact g32p_supplierForest_actual_030109
  · exact g32p_supplierForest_actual_030111
  · exact g32p_supplierForest_actual_030117
  · exact g32p_supplierForest_actual_030160
  · exact g32p_supplierForest_actual_030179
  · exact g32p_supplierForest_actual_030226
  · exact g32p_supplierForest_actual_030245
  · exact g32p_supplierForest_actual_030249
  · exact g32p_supplierForest_actual_030259
  · exact g32p_supplierForest_actual_030287
  · exact g32p_supplierForest_actual_030317
  · exact g32p_supplierForest_actual_030394
  · exact g32p_supplierForest_actual_030403
  · exact g32p_supplierForest_actual_030419
  · exact g32p_supplierForest_actual_030420
  · exact g32p_supplierForest_actual_030458
  · exact g32p_supplierForest_actual_030486
  · exact g32p_supplierForest_actual_030488
  · exact g32p_supplierForest_actual_030499
  · exact g32p_supplierForest_actual_030543
  · exact g32p_supplierForest_actual_030562
  · exact g32p_supplierForest_actual_030583
  · exact g32p_supplierForest_actual_030602
  · exact g32p_supplierForest_actual_030700
  · exact g32p_supplierForest_actual_030734
  · exact g32p_supplierForest_actual_030737
  · exact g32p_supplierForest_actual_030792
  · exact g32p_supplierForest_actual_030800
  · exact g32p_supplierForest_actual_030822
  · exact g32p_supplierForest_actual_030837
  · exact g32p_supplierForest_actual_030850
  · exact g32p_supplierForest_actual_030932
  · exact g32p_supplierForest_actual_030968
  · exact g32p_supplierForest_actual_031031
  · exact g32p_supplierForest_actual_031046
  · exact g32p_supplierForest_actual_031052
  · exact g32p_supplierForest_actual_031082
  · exact g32p_supplierForest_actual_031087
  · exact g32p_supplierForest_actual_031109
  · exact g32p_supplierForest_actual_031123
  · exact g32p_supplierForest_actual_031125
  · exact g32p_supplierForest_actual_031129
  · exact g32p_supplierForest_actual_031134
  · exact g32p_supplierForest_actual_031175
  · exact g32p_supplierForest_actual_031209
  · exact g32p_supplierForest_actual_031247
  · exact g32p_supplierForest_actual_031257
  · exact g32p_supplierForest_actual_031362
  · exact g32p_supplierForest_actual_031390
  · exact g32p_supplierForest_actual_031458
  · exact g32p_supplierForest_actual_031491
  · exact g32p_supplierForest_actual_031531
  · exact g32p_supplierForest_actual_031597
  · exact g32p_supplierForest_actual_031656
  · exact g32p_supplierForest_actual_031757
  · exact g32p_supplierForest_actual_031759
  · exact g32p_supplierForest_actual_031790
  · exact g32p_supplierForest_actual_031802
  · exact g32p_supplierForest_actual_031810
  · exact g32p_supplierForest_actual_031821
  · exact g32p_supplierForest_actual_031923
  · exact g32p_supplierForest_actual_031926
  · exact g32p_supplierForest_actual_031979
  · exact g32p_supplierForest_actual_032086
  · exact g32p_supplierForest_actual_032094
  · exact g32p_supplierForest_actual_032107
  · exact g32p_supplierForest_actual_032112
  · exact g32p_supplierForest_actual_032113
  · exact g32p_supplierForest_actual_032132
  · exact g32p_supplierForest_actual_032172
  · exact g32p_supplierForest_actual_032176
  · exact g32p_supplierForest_actual_032251
  · exact g32p_supplierForest_actual_032330
  · exact g32p_supplierForest_actual_032373
  · exact g32p_supplierForest_actual_032441
  · exact g32p_supplierForest_actual_032445
  · exact g32p_supplierForest_actual_032470
  · exact g32p_supplierForest_actual_032478
  · exact g32p_supplierForest_actual_032518
  · exact g32p_supplierForest_actual_032526
  · exact g32p_supplierForest_actual_032621
  · exact g32p_supplierForest_actual_032631
  · exact g32p_supplierForest_actual_032672
  · exact g32p_supplierForest_actual_032692
  · exact g32p_supplierForest_actual_032699
  · exact g32p_supplierForest_actual_032734
  · exact g32p_supplierForest_actual_032806
  · exact g32p_supplierForest_actual_032808
  · exact g32p_supplierForest_actual_032853
  · exact g32p_supplierForest_actual_032896
  · exact g32p_supplierForest_actual_032975
  · exact g32p_supplierForest_actual_033009
  · exact g32p_supplierForest_actual_033025
  · exact g32p_supplierForest_actual_033122
  · exact g32p_supplierForest_actual_033179
  · exact g32p_supplierForest_actual_033201
  · exact g32p_supplierForest_actual_033303
  · exact g32p_supplierForest_actual_033308
  · exact g32p_supplierForest_actual_033406
  · exact g32p_supplierForest_actual_033438
  · exact g32p_supplierForest_actual_033486
  · exact g32p_supplierForest_actual_033520
  · exact g32p_supplierForest_actual_033541
  · exact g32p_supplierForest_actual_033549
  · exact g32p_supplierForest_actual_033579
  · exact g32p_supplierForest_actual_033690
  · exact g32p_supplierForest_actual_033721
  · exact g32p_supplierForest_actual_033742
  · exact g32p_supplierForest_actual_033812
  · exact g32p_supplierForest_actual_033855
  · exact g32p_supplierForest_actual_033863
  · exact g32p_supplierForest_actual_033945
  · exact g32p_supplierForest_actual_033979
  · exact g32p_supplierForest_actual_034005
  · exact g32p_supplierForest_actual_034033
  · exact g32p_supplierForest_actual_034131
  · exact g32p_supplierForest_actual_034197
  · exact g32p_supplierForest_actual_034299
  · exact g32p_supplierForest_actual_034330
  · exact g32p_supplierForest_actual_034380
  · exact g32p_supplierForest_actual_034414
  · exact g32p_supplierForest_actual_034475
  · exact g32p_supplierForest_actual_034484
  · exact g32p_supplierForest_actual_034498
  · exact g32p_supplierForest_actual_034536
  · exact g32p_supplierForest_actual_034554
  · exact g32p_supplierForest_actual_034589
  · exact g32p_supplierForest_actual_034628
  · exact g32p_supplierForest_actual_034664
  · exact g32p_supplierForest_actual_034760
  · exact g32p_supplierForest_actual_034764
  · exact g32p_supplierForest_actual_034769
  · exact g32p_supplierForest_actual_034800
  · exact g32p_supplierForest_actual_034825
  · exact g32p_supplierForest_actual_034829
  · exact g32p_supplierForest_actual_034863
  · exact g32p_supplierForest_actual_035002
  · exact g32p_supplierForest_actual_035072
  · exact g32p_supplierForest_actual_035157
  · exact g32p_supplierForest_actual_035167
  · exact g32p_supplierForest_actual_035171
  · exact g32p_supplierForest_actual_035183
  · exact g32p_supplierForest_actual_035208
  · exact g32p_supplierForest_actual_035213
  · exact g32p_supplierForest_actual_035241
  · exact g32p_supplierForest_actual_035246
  · exact g32p_supplierForest_actual_035303
  · exact g32p_supplierForest_actual_035316
  · exact g32p_supplierForest_actual_035344
  · exact g32p_supplierForest_actual_035346
  · exact g32p_supplierForest_actual_035376
  · exact g32p_supplierForest_actual_035403
  · exact g32p_supplierForest_actual_035442
  · exact g32p_supplierForest_actual_035511
  · exact g32p_supplierForest_actual_035524
  · exact g32p_supplierForest_actual_035526
  · exact g32p_supplierForest_actual_035679
  · exact g32p_supplierForest_actual_035683
  · exact g32p_supplierForest_actual_035703
  · exact g32p_supplierForest_actual_035705
  · exact g32p_supplierForest_actual_035714
  · exact g32p_supplierForest_actual_035717
  · exact g32p_supplierForest_actual_035735
  · exact g32p_supplierForest_actual_035743
  · exact g32p_supplierForest_actual_035787
  · exact g32p_supplierForest_actual_035791
  · exact g32p_supplierForest_actual_035832
  · exact g32p_supplierForest_actual_035962
  · exact g32p_supplierForest_actual_035976
  · exact g32p_supplierForest_actual_036033
  · exact g32p_supplierForest_actual_036052
  · exact g32p_supplierForest_actual_036077
  · exact g32p_supplierForest_actual_036131
  · exact g32p_supplierForest_actual_036145
  · exact g32p_supplierForest_actual_036184
  · exact g32p_supplierForest_actual_036226
  · exact g32p_supplierForest_actual_036467
  · exact g32p_supplierForest_actual_036468
  · exact g32p_supplierForest_actual_036504
  · exact g32p_supplierForest_actual_036505
  · exact g32p_supplierForest_actual_036559
  · exact g32p_supplierForest_actual_036646

def g32p_supplierForest_nodes_020 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_036648 else g32p_supplierForest_node_036708) else (if i.val < 3 then g32p_supplierForest_node_036744 else g32p_supplierForest_node_036773)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_036775 else g32p_supplierForest_node_036786) else (if i.val < 7 then g32p_supplierForest_node_036804 else g32p_supplierForest_node_036813))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_036818 else g32p_supplierForest_node_036820) else (if i.val < 11 then g32p_supplierForest_node_036852 else g32p_supplierForest_node_036892)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_036893 else g32p_supplierForest_node_036933) else (if i.val < 15 then g32p_supplierForest_node_036956 else g32p_supplierForest_node_036988)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_037002 else g32p_supplierForest_node_037215) else (if i.val < 19 then g32p_supplierForest_node_037238 else g32p_supplierForest_node_037271)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_037305 else g32p_supplierForest_node_037366) else (if i.val < 23 then g32p_supplierForest_node_037370 else g32p_supplierForest_node_037377))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_037380 else g32p_supplierForest_node_037393) else (if i.val < 27 then g32p_supplierForest_node_037407 else g32p_supplierForest_node_037463)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_037467 else g32p_supplierForest_node_037553) else (if i.val < 31 then g32p_supplierForest_node_037618 else g32p_supplierForest_node_037625))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_037643 else g32p_supplierForest_node_037841) else (if i.val < 35 then g32p_supplierForest_node_037846 else g32p_supplierForest_node_037855)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_037857 else g32p_supplierForest_node_037870) else (if i.val < 39 then g32p_supplierForest_node_037880 else g32p_supplierForest_node_037946))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_038043 else g32p_supplierForest_node_038072) else (if i.val < 43 then g32p_supplierForest_node_038107 else g32p_supplierForest_node_038145)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_038146 else g32p_supplierForest_node_038149) else (if i.val < 47 then g32p_supplierForest_node_038152 else g32p_supplierForest_node_038154)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_038183 else g32p_supplierForest_node_038207) else (if i.val < 51 then g32p_supplierForest_node_038291 else g32p_supplierForest_node_038304)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_038333 else g32p_supplierForest_node_038417) else (if i.val < 55 then g32p_supplierForest_node_038460 else g32p_supplierForest_node_038466))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_038481 else g32p_supplierForest_node_038492) else (if i.val < 59 then g32p_supplierForest_node_038522 else g32p_supplierForest_node_038527)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_038536 else g32p_supplierForest_node_038541) else (if i.val < 63 then g32p_supplierForest_node_038545 else g32p_supplierForest_node_038661)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_038693 else g32p_supplierForest_node_038707) else (if i.val < 67 then g32p_supplierForest_node_038722 else g32p_supplierForest_node_038725)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_038727 else g32p_supplierForest_node_038733) else (if i.val < 71 then g32p_supplierForest_node_038735 else g32p_supplierForest_node_038786))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_038791 else g32p_supplierForest_node_038804) else (if i.val < 75 then g32p_supplierForest_node_038819 else g32p_supplierForest_node_038904)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_038918 else g32p_supplierForest_node_038964) else (if i.val < 79 then g32p_supplierForest_node_038966 else g32p_supplierForest_node_039077)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_039094 else g32p_supplierForest_node_039128) else (if i.val < 83 then g32p_supplierForest_node_039138 else g32p_supplierForest_node_039244)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_039320 else g32p_supplierForest_node_039345) else (if i.val < 87 then g32p_supplierForest_node_039378 else g32p_supplierForest_node_039407))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_039408 else g32p_supplierForest_node_039493) else (if i.val < 91 then g32p_supplierForest_node_039497 else g32p_supplierForest_node_039518)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_039527 else g32p_supplierForest_node_039535) else (if i.val < 95 then g32p_supplierForest_node_039544 else g32p_supplierForest_node_039565))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_039581 else g32p_supplierForest_node_039603) else (if i.val < 99 then g32p_supplierForest_node_039604 else g32p_supplierForest_node_039607)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_039646 else g32p_supplierForest_node_039657) else (if i.val < 103 then g32p_supplierForest_node_039678 else g32p_supplierForest_node_039758))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_039770 else g32p_supplierForest_node_039815) else (if i.val < 107 then g32p_supplierForest_node_039912 else g32p_supplierForest_node_039973)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_039979 else g32p_supplierForest_node_040015) else (if i.val < 111 then g32p_supplierForest_node_040016 else g32p_supplierForest_node_040153)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_040199 else g32p_supplierForest_node_040202) else (if i.val < 115 then g32p_supplierForest_node_040221 else g32p_supplierForest_node_040227)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_040274 else g32p_supplierForest_node_040307) else (if i.val < 119 then g32p_supplierForest_node_040366 else g32p_supplierForest_node_040379))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_040383 else g32p_supplierForest_node_040407) else (if i.val < 123 then g32p_supplierForest_node_040414 else g32p_supplierForest_node_040430)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_040433 else g32p_supplierForest_node_040436) else (if i.val < 127 then g32p_supplierForest_node_040466 else g32p_supplierForest_node_040467))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_040470 else g32p_supplierForest_node_040472) else (if i.val < 131 then g32p_supplierForest_node_040477 else g32p_supplierForest_node_040565)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_040627 else g32p_supplierForest_node_040662) else (if i.val < 135 then g32p_supplierForest_node_040686 else g32p_supplierForest_node_040717))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_040724 else g32p_supplierForest_node_040736) else (if i.val < 139 then g32p_supplierForest_node_040743 else g32p_supplierForest_node_040788)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_040796 else g32p_supplierForest_node_040821) else (if i.val < 143 then g32p_supplierForest_node_040828 else g32p_supplierForest_node_040834)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_040838 else g32p_supplierForest_node_040841) else (if i.val < 147 then g32p_supplierForest_node_040853 else g32p_supplierForest_node_040854)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_040861 else g32p_supplierForest_node_040886) else (if i.val < 151 then g32p_supplierForest_node_040943 else g32p_supplierForest_node_040978))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_040991 else g32p_supplierForest_node_041074) else (if i.val < 155 then g32p_supplierForest_node_041102 else g32p_supplierForest_node_041105)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_041134 else g32p_supplierForest_node_041171) else (if i.val < 159 then g32p_supplierForest_node_041179 else g32p_supplierForest_node_041214))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_041273 else g32p_supplierForest_node_041305) else (if i.val < 163 then g32p_supplierForest_node_041375 else g32p_supplierForest_node_041383)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_041392 else g32p_supplierForest_node_041425) else (if i.val < 167 then g32p_supplierForest_node_041463 else g32p_supplierForest_node_041477))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_041479 else g32p_supplierForest_node_041504) else (if i.val < 171 then g32p_supplierForest_node_041528 else g32p_supplierForest_node_041544)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_041559 else g32p_supplierForest_node_041585) else (if i.val < 175 then g32p_supplierForest_node_041616 else g32p_supplierForest_node_041627)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_041629 else g32p_supplierForest_node_041682) else (if i.val < 179 then g32p_supplierForest_node_041707 else g32p_supplierForest_node_041714)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_041755 else g32p_supplierForest_node_041822) else (if i.val < 183 then g32p_supplierForest_node_041826 else g32p_supplierForest_node_041869))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_041899 else g32p_supplierForest_node_041932) else (if i.val < 187 then g32p_supplierForest_node_041959 else g32p_supplierForest_node_041962)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_041965 else g32p_supplierForest_node_042099) else (if i.val < 191 then g32p_supplierForest_node_042213 else g32p_supplierForest_node_042215)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_042265 else g32p_supplierForest_node_042380) else (if i.val < 195 then g32p_supplierForest_node_042434 else g32p_supplierForest_node_042461)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_042584 else g32p_supplierForest_node_042603) else (if i.val < 199 then g32p_supplierForest_node_042650 else g32p_supplierForest_node_042658))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_042708 else g32p_supplierForest_node_042713) else (if i.val < 203 then g32p_supplierForest_node_042738 else g32p_supplierForest_node_042784)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_042863 else g32p_supplierForest_node_042938) else (if i.val < 207 then g32p_supplierForest_node_042942 else g32p_supplierForest_node_042970)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_043051 else g32p_supplierForest_node_043052) else (if i.val < 211 then g32p_supplierForest_node_043088 else g32p_supplierForest_node_043114)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_043175 else g32p_supplierForest_node_043204) else (if i.val < 215 then g32p_supplierForest_node_043246 else g32p_supplierForest_node_043290))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_043318 else g32p_supplierForest_node_043329) else (if i.val < 219 then g32p_supplierForest_node_043409 else g32p_supplierForest_node_043437)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_043446 else g32p_supplierForest_node_043494) else (if i.val < 223 then g32p_supplierForest_node_043561 else g32p_supplierForest_node_043583))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_043588 else g32p_supplierForest_node_043629) else (if i.val < 227 then g32p_supplierForest_node_043642 else g32p_supplierForest_node_043650)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_043652 else g32p_supplierForest_node_043663) else (if i.val < 231 then g32p_supplierForest_node_043677 else g32p_supplierForest_node_043803))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_043865 else g32p_supplierForest_node_043899) else (if i.val < 235 then g32p_supplierForest_node_043922 else g32p_supplierForest_node_043970)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_044003 else g32p_supplierForest_node_044077) else (if i.val < 239 then g32p_supplierForest_node_044128 else g32p_supplierForest_node_044146)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_044153 else g32p_supplierForest_node_044176) else (if i.val < 243 then g32p_supplierForest_node_044189 else g32p_supplierForest_node_044239)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_044349 else g32p_supplierForest_node_044419) else (if i.val < 247 then g32p_supplierForest_node_044427 else g32p_supplierForest_node_044480))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_044571 else g32p_supplierForest_node_044575) else (if i.val < 251 then g32p_supplierForest_node_044587 else g32p_supplierForest_node_044604)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_044629 else g32p_supplierForest_node_044673) else (if i.val < 255 then g32p_supplierForest_node_044770 else g32p_supplierForest_node_044826))))))))

def g32p_supplierForest_classes_020 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 60 else 16) else (if i.val < 3 then 16 else 16)) else (if i.val < 6 then (if i.val < 5 then 15 else 15) else (if i.val < 7 then 57 else 58))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 30 else 14) else (if i.val < 11 then 31 else 57)) else (if i.val < 14 then (if i.val < 13 then 57 else 4) else (if i.val < 15 then 2 else 17)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 3 else 30) else (if i.val < 19 then 62 else 34)) else (if i.val < 22 then (if i.val < 21 then 3 else 14) else (if i.val < 23 then 16 else 34))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 4 else 36) else (if i.val < 27 then 34 else 58)) else (if i.val < 30 then (if i.val < 29 then 58 else 16) else (if i.val < 31 then 16 else 16))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 34 else 14) else (if i.val < 35 then 57 else 29)) else (if i.val < 38 then (if i.val < 37 then 63 else 16) else (if i.val < 39 then 15 else 63))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 29 else 29) else (if i.val < 43 then 15 else 15)) else (if i.val < 46 then (if i.val < 45 then 33 else 16) else (if i.val < 47 then 15 else 16)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 30 else 60) else (if i.val < 51 then 30 else 57)) else (if i.val < 54 then (if i.val < 53 then 63 else 4) else (if i.val < 55 then 61 else 32))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 36 else 15) else (if i.val < 59 then 16 else 30)) else (if i.val < 62 then (if i.val < 61 then 64 else 57) else (if i.val < 63 then 16 else 32)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 16 else 16) else (if i.val < 67 then 58 else 16)) else (if i.val < 70 then (if i.val < 69 then 58 else 17) else (if i.val < 71 then 59 else 29))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 34 else 36) else (if i.val < 75 then 61 else 17)) else (if i.val < 78 then (if i.val < 77 then 58 else 33) else (if i.val < 79 then 58 else 33)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 33 else 59) else (if i.val < 83 then 30 else 16)) else (if i.val < 86 then (if i.val < 85 then 32 else 16) else (if i.val < 87 then 34 else 59))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 15 else 31) else (if i.val < 91 then 14 else 57)) else (if i.val < 94 then (if i.val < 93 then 57 else 58) else (if i.val < 95 then 63 else 16))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 36 else 30) else (if i.val < 99 then 32 else 64)) else (if i.val < 102 then (if i.val < 101 then 63 else 29) else (if i.val < 103 then 16 else 30))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 32 else 31) else (if i.val < 107 then 4 else 30)) else (if i.val < 110 then (if i.val < 109 then 14 else 36) else (if i.val < 111 then 16 else 14)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 30 else 29) else (if i.val < 115 then 59 else 30)) else (if i.val < 118 then (if i.val < 117 then 31 else 60) else (if i.val < 119 then 58 else 36))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 16 else 4) else (if i.val < 123 then 32 else 57)) else (if i.val < 126 then (if i.val < 125 then 58 else 16) else (if i.val < 127 then 32 else 30))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 35 else 30) else (if i.val < 131 then 14 else 65)) else (if i.val < 134 then (if i.val < 133 then 62 else 57) else (if i.val < 135 then 34 else 14))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 59 else 60) else (if i.val < 139 then 30 else 33)) else (if i.val < 142 then (if i.val < 141 then 60 else 61) else (if i.val < 143 then 63 else 32)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 62 else 17) else (if i.val < 147 then 59 else 34)) else (if i.val < 150 then (if i.val < 149 then 60 else 35) else (if i.val < 151 then 58 else 63))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 34 else 16) else (if i.val < 155 then 58 else 59)) else (if i.val < 158 then (if i.val < 157 then 60 else 63) else (if i.val < 159 then 58 else 64))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 65 else 36) else (if i.val < 163 then 34 else 16)) else (if i.val < 166 then (if i.val < 165 then 57 else 4) else (if i.val < 167 then 14 else 30))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 34 else 3) else (if i.val < 171 then 17 else 17)) else (if i.val < 174 then (if i.val < 173 then 35 else 14) else (if i.val < 175 then 14 else 34)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 14 else 33) else (if i.val < 179 then 16 else 15)) else (if i.val < 182 then (if i.val < 181 then 17 else 34) else (if i.val < 183 then 57 else 34))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 14 else 30) else (if i.val < 187 then 32 else 35)) else (if i.val < 190 then (if i.val < 189 then 33 else 34) else (if i.val < 191 then 59 else 32)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 34 else 36) else (if i.val < 195 then 30 else 30)) else (if i.val < 198 then (if i.val < 197 then 62 else 62) else (if i.val < 199 then 34 else 34))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 34 else 33) else (if i.val < 203 then 34 else 61)) else (if i.val < 206 then (if i.val < 205 then 35 else 15) else (if i.val < 207 then 30 else 30)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 30 else 58) else (if i.val < 211 then 57 else 16)) else (if i.val < 214 then (if i.val < 213 then 59 else 60) else (if i.val < 215 then 62 else 14))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 34 else 30) else (if i.val < 219 then 36 else 16)) else (if i.val < 222 then (if i.val < 221 then 65 else 63) else (if i.val < 223 then 65 else 30))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 63 else 64) else (if i.val < 227 then 34 else 36)) else (if i.val < 230 then (if i.val < 229 then 64 else 57) else (if i.val < 231 then 58 else 63))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 34 else 30) else (if i.val < 235 then 15 else 15)) else (if i.val < 238 then (if i.val < 237 then 17 else 29) else (if i.val < 239 then 29 else 57)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 30 else 62) else (if i.val < 243 then 17 else 16)) else (if i.val < 246 then (if i.val < 245 then 34 else 29) else (if i.val < 247 then 39 else 23))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 42 else 23) else (if i.val < 251 then 39 else 7)) else (if i.val < 254 then (if i.val < 253 then 21 else 38) else (if i.val < 255 then 21 else 41))))))))

theorem g32p_supplierForest_actual_020 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_020 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_020 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_036648
  · exact g32p_supplierForest_actual_036708
  · exact g32p_supplierForest_actual_036744
  · exact g32p_supplierForest_actual_036773
  · exact g32p_supplierForest_actual_036775
  · exact g32p_supplierForest_actual_036786
  · exact g32p_supplierForest_actual_036804
  · exact g32p_supplierForest_actual_036813
  · exact g32p_supplierForest_actual_036818
  · exact g32p_supplierForest_actual_036820
  · exact g32p_supplierForest_actual_036852
  · exact g32p_supplierForest_actual_036892
  · exact g32p_supplierForest_actual_036893
  · exact g32p_supplierForest_actual_036933
  · exact g32p_supplierForest_actual_036956
  · exact g32p_supplierForest_actual_036988
  · exact g32p_supplierForest_actual_037002
  · exact g32p_supplierForest_actual_037215
  · exact g32p_supplierForest_actual_037238
  · exact g32p_supplierForest_actual_037271
  · exact g32p_supplierForest_actual_037305
  · exact g32p_supplierForest_actual_037366
  · exact g32p_supplierForest_actual_037370
  · exact g32p_supplierForest_actual_037377
  · exact g32p_supplierForest_actual_037380
  · exact g32p_supplierForest_actual_037393
  · exact g32p_supplierForest_actual_037407
  · exact g32p_supplierForest_actual_037463
  · exact g32p_supplierForest_actual_037467
  · exact g32p_supplierForest_actual_037553
  · exact g32p_supplierForest_actual_037618
  · exact g32p_supplierForest_actual_037625
  · exact g32p_supplierForest_actual_037643
  · exact g32p_supplierForest_actual_037841
  · exact g32p_supplierForest_actual_037846
  · exact g32p_supplierForest_actual_037855
  · exact g32p_supplierForest_actual_037857
  · exact g32p_supplierForest_actual_037870
  · exact g32p_supplierForest_actual_037880
  · exact g32p_supplierForest_actual_037946
  · exact g32p_supplierForest_actual_038043
  · exact g32p_supplierForest_actual_038072
  · exact g32p_supplierForest_actual_038107
  · exact g32p_supplierForest_actual_038145
  · exact g32p_supplierForest_actual_038146
  · exact g32p_supplierForest_actual_038149
  · exact g32p_supplierForest_actual_038152
  · exact g32p_supplierForest_actual_038154
  · exact g32p_supplierForest_actual_038183
  · exact g32p_supplierForest_actual_038207
  · exact g32p_supplierForest_actual_038291
  · exact g32p_supplierForest_actual_038304
  · exact g32p_supplierForest_actual_038333
  · exact g32p_supplierForest_actual_038417
  · exact g32p_supplierForest_actual_038460
  · exact g32p_supplierForest_actual_038466
  · exact g32p_supplierForest_actual_038481
  · exact g32p_supplierForest_actual_038492
  · exact g32p_supplierForest_actual_038522
  · exact g32p_supplierForest_actual_038527
  · exact g32p_supplierForest_actual_038536
  · exact g32p_supplierForest_actual_038541
  · exact g32p_supplierForest_actual_038545
  · exact g32p_supplierForest_actual_038661
  · exact g32p_supplierForest_actual_038693
  · exact g32p_supplierForest_actual_038707
  · exact g32p_supplierForest_actual_038722
  · exact g32p_supplierForest_actual_038725
  · exact g32p_supplierForest_actual_038727
  · exact g32p_supplierForest_actual_038733
  · exact g32p_supplierForest_actual_038735
  · exact g32p_supplierForest_actual_038786
  · exact g32p_supplierForest_actual_038791
  · exact g32p_supplierForest_actual_038804
  · exact g32p_supplierForest_actual_038819
  · exact g32p_supplierForest_actual_038904
  · exact g32p_supplierForest_actual_038918
  · exact g32p_supplierForest_actual_038964
  · exact g32p_supplierForest_actual_038966
  · exact g32p_supplierForest_actual_039077
  · exact g32p_supplierForest_actual_039094
  · exact g32p_supplierForest_actual_039128
  · exact g32p_supplierForest_actual_039138
  · exact g32p_supplierForest_actual_039244
  · exact g32p_supplierForest_actual_039320
  · exact g32p_supplierForest_actual_039345
  · exact g32p_supplierForest_actual_039378
  · exact g32p_supplierForest_actual_039407
  · exact g32p_supplierForest_actual_039408
  · exact g32p_supplierForest_actual_039493
  · exact g32p_supplierForest_actual_039497
  · exact g32p_supplierForest_actual_039518
  · exact g32p_supplierForest_actual_039527
  · exact g32p_supplierForest_actual_039535
  · exact g32p_supplierForest_actual_039544
  · exact g32p_supplierForest_actual_039565
  · exact g32p_supplierForest_actual_039581
  · exact g32p_supplierForest_actual_039603
  · exact g32p_supplierForest_actual_039604
  · exact g32p_supplierForest_actual_039607
  · exact g32p_supplierForest_actual_039646
  · exact g32p_supplierForest_actual_039657
  · exact g32p_supplierForest_actual_039678
  · exact g32p_supplierForest_actual_039758
  · exact g32p_supplierForest_actual_039770
  · exact g32p_supplierForest_actual_039815
  · exact g32p_supplierForest_actual_039912
  · exact g32p_supplierForest_actual_039973
  · exact g32p_supplierForest_actual_039979
  · exact g32p_supplierForest_actual_040015
  · exact g32p_supplierForest_actual_040016
  · exact g32p_supplierForest_actual_040153
  · exact g32p_supplierForest_actual_040199
  · exact g32p_supplierForest_actual_040202
  · exact g32p_supplierForest_actual_040221
  · exact g32p_supplierForest_actual_040227
  · exact g32p_supplierForest_actual_040274
  · exact g32p_supplierForest_actual_040307
  · exact g32p_supplierForest_actual_040366
  · exact g32p_supplierForest_actual_040379
  · exact g32p_supplierForest_actual_040383
  · exact g32p_supplierForest_actual_040407
  · exact g32p_supplierForest_actual_040414
  · exact g32p_supplierForest_actual_040430
  · exact g32p_supplierForest_actual_040433
  · exact g32p_supplierForest_actual_040436
  · exact g32p_supplierForest_actual_040466
  · exact g32p_supplierForest_actual_040467
  · exact g32p_supplierForest_actual_040470
  · exact g32p_supplierForest_actual_040472
  · exact g32p_supplierForest_actual_040477
  · exact g32p_supplierForest_actual_040565
  · exact g32p_supplierForest_actual_040627
  · exact g32p_supplierForest_actual_040662
  · exact g32p_supplierForest_actual_040686
  · exact g32p_supplierForest_actual_040717
  · exact g32p_supplierForest_actual_040724
  · exact g32p_supplierForest_actual_040736
  · exact g32p_supplierForest_actual_040743
  · exact g32p_supplierForest_actual_040788
  · exact g32p_supplierForest_actual_040796
  · exact g32p_supplierForest_actual_040821
  · exact g32p_supplierForest_actual_040828
  · exact g32p_supplierForest_actual_040834
  · exact g32p_supplierForest_actual_040838
  · exact g32p_supplierForest_actual_040841
  · exact g32p_supplierForest_actual_040853
  · exact g32p_supplierForest_actual_040854
  · exact g32p_supplierForest_actual_040861
  · exact g32p_supplierForest_actual_040886
  · exact g32p_supplierForest_actual_040943
  · exact g32p_supplierForest_actual_040978
  · exact g32p_supplierForest_actual_040991
  · exact g32p_supplierForest_actual_041074
  · exact g32p_supplierForest_actual_041102
  · exact g32p_supplierForest_actual_041105
  · exact g32p_supplierForest_actual_041134
  · exact g32p_supplierForest_actual_041171
  · exact g32p_supplierForest_actual_041179
  · exact g32p_supplierForest_actual_041214
  · exact g32p_supplierForest_actual_041273
  · exact g32p_supplierForest_actual_041305
  · exact g32p_supplierForest_actual_041375
  · exact g32p_supplierForest_actual_041383
  · exact g32p_supplierForest_actual_041392
  · exact g32p_supplierForest_actual_041425
  · exact g32p_supplierForest_actual_041463
  · exact g32p_supplierForest_actual_041477
  · exact g32p_supplierForest_actual_041479
  · exact g32p_supplierForest_actual_041504
  · exact g32p_supplierForest_actual_041528
  · exact g32p_supplierForest_actual_041544
  · exact g32p_supplierForest_actual_041559
  · exact g32p_supplierForest_actual_041585
  · exact g32p_supplierForest_actual_041616
  · exact g32p_supplierForest_actual_041627
  · exact g32p_supplierForest_actual_041629
  · exact g32p_supplierForest_actual_041682
  · exact g32p_supplierForest_actual_041707
  · exact g32p_supplierForest_actual_041714
  · exact g32p_supplierForest_actual_041755
  · exact g32p_supplierForest_actual_041822
  · exact g32p_supplierForest_actual_041826
  · exact g32p_supplierForest_actual_041869
  · exact g32p_supplierForest_actual_041899
  · exact g32p_supplierForest_actual_041932
  · exact g32p_supplierForest_actual_041959
  · exact g32p_supplierForest_actual_041962
  · exact g32p_supplierForest_actual_041965
  · exact g32p_supplierForest_actual_042099
  · exact g32p_supplierForest_actual_042213
  · exact g32p_supplierForest_actual_042215
  · exact g32p_supplierForest_actual_042265
  · exact g32p_supplierForest_actual_042380
  · exact g32p_supplierForest_actual_042434
  · exact g32p_supplierForest_actual_042461
  · exact g32p_supplierForest_actual_042584
  · exact g32p_supplierForest_actual_042603
  · exact g32p_supplierForest_actual_042650
  · exact g32p_supplierForest_actual_042658
  · exact g32p_supplierForest_actual_042708
  · exact g32p_supplierForest_actual_042713
  · exact g32p_supplierForest_actual_042738
  · exact g32p_supplierForest_actual_042784
  · exact g32p_supplierForest_actual_042863
  · exact g32p_supplierForest_actual_042938
  · exact g32p_supplierForest_actual_042942
  · exact g32p_supplierForest_actual_042970
  · exact g32p_supplierForest_actual_043051
  · exact g32p_supplierForest_actual_043052
  · exact g32p_supplierForest_actual_043088
  · exact g32p_supplierForest_actual_043114
  · exact g32p_supplierForest_actual_043175
  · exact g32p_supplierForest_actual_043204
  · exact g32p_supplierForest_actual_043246
  · exact g32p_supplierForest_actual_043290
  · exact g32p_supplierForest_actual_043318
  · exact g32p_supplierForest_actual_043329
  · exact g32p_supplierForest_actual_043409
  · exact g32p_supplierForest_actual_043437
  · exact g32p_supplierForest_actual_043446
  · exact g32p_supplierForest_actual_043494
  · exact g32p_supplierForest_actual_043561
  · exact g32p_supplierForest_actual_043583
  · exact g32p_supplierForest_actual_043588
  · exact g32p_supplierForest_actual_043629
  · exact g32p_supplierForest_actual_043642
  · exact g32p_supplierForest_actual_043650
  · exact g32p_supplierForest_actual_043652
  · exact g32p_supplierForest_actual_043663
  · exact g32p_supplierForest_actual_043677
  · exact g32p_supplierForest_actual_043803
  · exact g32p_supplierForest_actual_043865
  · exact g32p_supplierForest_actual_043899
  · exact g32p_supplierForest_actual_043922
  · exact g32p_supplierForest_actual_043970
  · exact g32p_supplierForest_actual_044003
  · exact g32p_supplierForest_actual_044077
  · exact g32p_supplierForest_actual_044128
  · exact g32p_supplierForest_actual_044146
  · exact g32p_supplierForest_actual_044153
  · exact g32p_supplierForest_actual_044176
  · exact g32p_supplierForest_actual_044189
  · exact g32p_supplierForest_actual_044239
  · exact g32p_supplierForest_actual_044349
  · exact g32p_supplierForest_actual_044419
  · exact g32p_supplierForest_actual_044427
  · exact g32p_supplierForest_actual_044480
  · exact g32p_supplierForest_actual_044571
  · exact g32p_supplierForest_actual_044575
  · exact g32p_supplierForest_actual_044587
  · exact g32p_supplierForest_actual_044604
  · exact g32p_supplierForest_actual_044629
  · exact g32p_supplierForest_actual_044673
  · exact g32p_supplierForest_actual_044770
  · exact g32p_supplierForest_actual_044826

def g32p_supplierForest_nodes_021 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_044941 else g32p_supplierForest_node_044962) else (if i.val < 3 then g32p_supplierForest_node_044972 else g32p_supplierForest_node_044986)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_045005 else g32p_supplierForest_node_045084) else (if i.val < 7 then g32p_supplierForest_node_045092 else g32p_supplierForest_node_045124))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_045140 else g32p_supplierForest_node_045155) else (if i.val < 11 then g32p_supplierForest_node_045167 else g32p_supplierForest_node_045169)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_045191 else g32p_supplierForest_node_045195) else (if i.val < 15 then g32p_supplierForest_node_045286 else g32p_supplierForest_node_045294)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_045334 else g32p_supplierForest_node_045341) else (if i.val < 19 then g32p_supplierForest_node_045370 else g32p_supplierForest_node_045398)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_045433 else g32p_supplierForest_node_045475) else (if i.val < 23 then g32p_supplierForest_node_045477 else g32p_supplierForest_node_045566))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_045598 else g32p_supplierForest_node_045629) else (if i.val < 27 then g32p_supplierForest_node_045639 else g32p_supplierForest_node_045705)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_045786 else g32p_supplierForest_node_045813) else (if i.val < 31 then g32p_supplierForest_node_045883 else g32p_supplierForest_node_045894))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_045959 else g32p_supplierForest_node_045971) else (if i.val < 35 then g32p_supplierForest_node_045975 else g32p_supplierForest_node_045976)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_046061 else g32p_supplierForest_node_046079) else (if i.val < 39 then g32p_supplierForest_node_046104 else g32p_supplierForest_node_046106))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_046156 else g32p_supplierForest_node_046161) else (if i.val < 43 then g32p_supplierForest_node_046177 else g32p_supplierForest_node_046183)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_046202 else g32p_supplierForest_node_046209) else (if i.val < 47 then g32p_supplierForest_node_046230 else g32p_supplierForest_node_046250)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_046255 else g32p_supplierForest_node_046261) else (if i.val < 51 then g32p_supplierForest_node_046347 else g32p_supplierForest_node_046421)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_046425 else g32p_supplierForest_node_046449) else (if i.val < 55 then g32p_supplierForest_node_046461 else g32p_supplierForest_node_046481))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_046495 else g32p_supplierForest_node_046589) else (if i.val < 59 then g32p_supplierForest_node_046597 else g32p_supplierForest_node_046625)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_046639 else g32p_supplierForest_node_046660) else (if i.val < 63 then g32p_supplierForest_node_046684 else g32p_supplierForest_node_046693)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_046753 else g32p_supplierForest_node_046755) else (if i.val < 67 then g32p_supplierForest_node_046756 else g32p_supplierForest_node_046779)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_046790 else g32p_supplierForest_node_046799) else (if i.val < 71 then g32p_supplierForest_node_046901 else g32p_supplierForest_node_046970))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_046973 else g32p_supplierForest_node_046991) else (if i.val < 75 then g32p_supplierForest_node_047022 else g32p_supplierForest_node_047052)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_047059 else g32p_supplierForest_node_047063) else (if i.val < 79 then g32p_supplierForest_node_047070 else g32p_supplierForest_node_047093)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_047102 else g32p_supplierForest_node_047216) else (if i.val < 83 then g32p_supplierForest_node_047232 else g32p_supplierForest_node_047258)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_047262 else g32p_supplierForest_node_047309) else (if i.val < 87 then g32p_supplierForest_node_047421 else g32p_supplierForest_node_047495))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_047550 else g32p_supplierForest_node_047574) else (if i.val < 91 then g32p_supplierForest_node_047581 else g32p_supplierForest_node_047589)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_047609 else g32p_supplierForest_node_047618) else (if i.val < 95 then g32p_supplierForest_node_047664 else g32p_supplierForest_node_047691))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_047696 else g32p_supplierForest_node_047702) else (if i.val < 99 then g32p_supplierForest_node_047727 else g32p_supplierForest_node_047730)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_047731 else g32p_supplierForest_node_047757) else (if i.val < 103 then g32p_supplierForest_node_047783 else g32p_supplierForest_node_047823))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_047865 else g32p_supplierForest_node_047904) else (if i.val < 107 then g32p_supplierForest_node_047923 else g32p_supplierForest_node_047958)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_047962 else g32p_supplierForest_node_047993) else (if i.val < 111 then g32p_supplierForest_node_048039 else g32p_supplierForest_node_048056)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_048082 else g32p_supplierForest_node_048110) else (if i.val < 115 then g32p_supplierForest_node_048184 else g32p_supplierForest_node_048195)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_048208 else g32p_supplierForest_node_048280) else (if i.val < 119 then g32p_supplierForest_node_048297 else g32p_supplierForest_node_048303))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_048332 else g32p_supplierForest_node_048334) else (if i.val < 123 then g32p_supplierForest_node_048346 else g32p_supplierForest_node_048529)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_048569 else g32p_supplierForest_node_048772) else (if i.val < 127 then g32p_supplierForest_node_048924 else g32p_supplierForest_node_048964))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_049060 else g32p_supplierForest_node_049156) else (if i.val < 131 then g32p_supplierForest_node_049266 else g32p_supplierForest_node_049324)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_049325 else g32p_supplierForest_node_049327) else (if i.val < 135 then g32p_supplierForest_node_049333 else g32p_supplierForest_node_049375))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_049378 else g32p_supplierForest_node_049398) else (if i.val < 139 then g32p_supplierForest_node_049489 else g32p_supplierForest_node_049573)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_049581 else g32p_supplierForest_node_049608) else (if i.val < 143 then g32p_supplierForest_node_049649 else g32p_supplierForest_node_049706)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_049849 else g32p_supplierForest_node_049850) else (if i.val < 147 then g32p_supplierForest_node_049858 else g32p_supplierForest_node_049859)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_049982 else g32p_supplierForest_node_050005) else (if i.val < 151 then g32p_supplierForest_node_050007 else g32p_supplierForest_node_050017))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_050130 else g32p_supplierForest_node_050132) else (if i.val < 155 then g32p_supplierForest_node_050151 else g32p_supplierForest_node_050200)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_050254 else g32p_supplierForest_node_050287) else (if i.val < 159 then g32p_supplierForest_node_050378 else g32p_supplierForest_node_050520))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_050544 else g32p_supplierForest_node_050585) else (if i.val < 163 then g32p_supplierForest_node_050672 else g32p_supplierForest_node_050687)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_050702 else g32p_supplierForest_node_050703) else (if i.val < 167 then g32p_supplierForest_node_050728 else g32p_supplierForest_node_050798))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_050854 else g32p_supplierForest_node_050891) else (if i.val < 171 then g32p_supplierForest_node_050929 else g32p_supplierForest_node_050977)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_050997 else g32p_supplierForest_node_051059) else (if i.val < 175 then g32p_supplierForest_node_051068 else g32p_supplierForest_node_051071)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_051094 else g32p_supplierForest_node_051139) else (if i.val < 179 then g32p_supplierForest_node_051144 else g32p_supplierForest_node_051150)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_051163 else g32p_supplierForest_node_051164) else (if i.val < 183 then g32p_supplierForest_node_051190 else g32p_supplierForest_node_051212))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_051240 else g32p_supplierForest_node_051304) else (if i.val < 187 then g32p_supplierForest_node_051337 else g32p_supplierForest_node_051430)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_051456 else g32p_supplierForest_node_051483) else (if i.val < 191 then g32p_supplierForest_node_051484 else g32p_supplierForest_node_051507)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_051543 else g32p_supplierForest_node_051635) else (if i.val < 195 then g32p_supplierForest_node_051642 else g32p_supplierForest_node_051715)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_051780 else g32p_supplierForest_node_051811) else (if i.val < 199 then g32p_supplierForest_node_051818 else g32p_supplierForest_node_051869))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_051905 else g32p_supplierForest_node_051910) else (if i.val < 203 then g32p_supplierForest_node_051957 else g32p_supplierForest_node_051983)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_052007 else g32p_supplierForest_node_052017) else (if i.val < 207 then g32p_supplierForest_node_052021 else g32p_supplierForest_node_052027)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_052028 else g32p_supplierForest_node_052160) else (if i.val < 211 then g32p_supplierForest_node_052184 else g32p_supplierForest_node_052195)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_052206 else g32p_supplierForest_node_052238) else (if i.val < 215 then g32p_supplierForest_node_052317 else g32p_supplierForest_node_052334))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_052352 else g32p_supplierForest_node_052411) else (if i.val < 219 then g32p_supplierForest_node_052433 else g32p_supplierForest_node_052632)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_052647 else g32p_supplierForest_node_052805) else (if i.val < 223 then g32p_supplierForest_node_052819 else g32p_supplierForest_node_052844))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_052846 else g32p_supplierForest_node_052911) else (if i.val < 227 then g32p_supplierForest_node_052965 else g32p_supplierForest_node_052997)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_053002 else g32p_supplierForest_node_053024) else (if i.val < 231 then g32p_supplierForest_node_053043 else g32p_supplierForest_node_053057))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_053060 else g32p_supplierForest_node_053094) else (if i.val < 235 then g32p_supplierForest_node_053098 else g32p_supplierForest_node_053122)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_053180 else g32p_supplierForest_node_053198) else (if i.val < 239 then g32p_supplierForest_node_053200 else g32p_supplierForest_node_053213)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_053240 else g32p_supplierForest_node_053312) else (if i.val < 243 then g32p_supplierForest_node_053339 else g32p_supplierForest_node_053403)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_053422 else g32p_supplierForest_node_053488) else (if i.val < 247 then g32p_supplierForest_node_053515 else g32p_supplierForest_node_053528))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_053577 else g32p_supplierForest_node_053601) else (if i.val < 251 then g32p_supplierForest_node_053607 else g32p_supplierForest_node_053618)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_053628 else g32p_supplierForest_node_053645) else (if i.val < 255 then g32p_supplierForest_node_053701 else g32p_supplierForest_node_053751))))))))

def g32p_supplierForest_classes_021 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 41 else 39) else (if i.val < 3 then 68 else 40)) else (if i.val < 6 then (if i.val < 5 then 39 else 39) else (if i.val < 7 then 41 else 69))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 38) else (if i.val < 11 then 38 else 73)) else (if i.val < 14 then (if i.val < 13 then 74 else 69) else (if i.val < 15 then 67 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 41 else 38) else (if i.val < 19 then 40 else 24)) else (if i.val < 22 then (if i.val < 21 then 41 else 70) else (if i.val < 23 then 70 else 70))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 23 else 24) else (if i.val < 27 then 70 else 38)) else (if i.val < 30 then (if i.val < 29 then 21 else 22) else (if i.val < 31 then 19 else 21))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 20 else 71) else (if i.val < 35 then 70 else 71)) else (if i.val < 38 then (if i.val < 37 then 21 else 39) else (if i.val < 39 then 38 else 22))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 38) else (if i.val < 43 then 21 else 40)) else (if i.val < 46 then (if i.val < 45 then 22 else 21) else (if i.val < 47 then 18 else 22)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 22 else 22) else (if i.val < 51 then 20 else 20)) else (if i.val < 54 then (if i.val < 53 then 22 else 70) else (if i.val < 55 then 22 else 5))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 5) else (if i.val < 59 then 70 else 7)) else (if i.val < 62 then (if i.val < 61 then 69 else 18) else (if i.val < 63 then 6 else 43)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 38 else 7) else (if i.val < 67 then 19 else 38)) else (if i.val < 70 then (if i.val < 69 then 38 else 7) else (if i.val < 71 then 24 else 24))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 70 else 38) else (if i.val < 75 then 38 else 23)) else (if i.val < 78 then (if i.val < 77 then 24 else 22) else (if i.val < 79 then 21 else 20)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 69 else 68) else (if i.val < 83 then 42 else 42)) else (if i.val < 86 then (if i.val < 85 then 22 else 70) else (if i.val < 87 then 5 else 21))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 18 else 68) else (if i.val < 91 then 70 else 6)) else (if i.val < 94 then (if i.val < 93 then 71 else 40) else (if i.val < 95 then 7 else 39))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 69 else 7) else (if i.val < 99 then 68 else 24)) else (if i.val < 102 then (if i.val < 101 then 40 else 40) else (if i.val < 103 then 74 else 74))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 23 else 73) else (if i.val < 107 then 74 else 70)) else (if i.val < 110 then (if i.val < 109 then 7 else 70) else (if i.val < 111 then 38 else 7)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 38 else 22) else (if i.val < 115 then 38 else 74)) else (if i.val < 118 then (if i.val < 117 then 69 else 24) else (if i.val < 119 then 22 else 71))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 22 else 38) else (if i.val < 123 then 22 else 69)) else (if i.val < 126 then (if i.val < 125 then 70 else 19) else (if i.val < 127 then 70 else 22))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 42 else 20) else (if i.val < 131 then 22 else 43)) else (if i.val < 134 then (if i.val < 133 then 39 else 22) else (if i.val < 135 then 43 else 6))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 21 else 40) else (if i.val < 139 then 7 else 43)) else (if i.val < 142 then (if i.val < 141 then 19 else 40) else (if i.val < 143 then 24 else 5)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 7 else 39) else (if i.val < 147 then 5 else 5)) else (if i.val < 150 then (if i.val < 149 then 40 else 39) else (if i.val < 151 then 20 else 21))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 39 else 38) else (if i.val < 155 then 40 else 41)) else (if i.val < 158 then (if i.val < 157 then 6 else 41) else (if i.val < 159 then 40 else 38))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 22 else 39) else (if i.val < 163 then 23 else 23)) else (if i.val < 166 then (if i.val < 165 then 24 else 20) else (if i.val < 167 then 24 else 7))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 20 else 74) else (if i.val < 171 then 23 else 40)) else (if i.val < 174 then (if i.val < 173 then 6 else 21) else (if i.val < 175 then 43 else 21)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 40) else (if i.val < 179 then 22 else 70)) else (if i.val < 182 then (if i.val < 181 then 20 else 20) else (if i.val < 183 then 7 else 39))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 39 else 40) else (if i.val < 187 then 40 else 69)) else (if i.val < 190 then (if i.val < 189 then 69 else 70) else (if i.val < 191 then 68 else 43)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 70 else 40) else (if i.val < 195 then 44 else 71)) else (if i.val < 198 then (if i.val < 197 then 41 else 38) else (if i.val < 199 then 69 else 74))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 68 else 74) else (if i.val < 203 then 71 else 74)) else (if i.val < 206 then (if i.val < 205 then 7 else 73) else (if i.val < 207 then 23 else 74)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 74 else 78) else (if i.val < 211 then 40 else 42)) else (if i.val < 214 then (if i.val < 213 then 43 else 38) else (if i.val < 215 then 69 else 42))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 67 else 40) else (if i.val < 219 then 40 else 43)) else (if i.val < 222 then (if i.val < 221 then 22 else 70) else (if i.val < 223 then 22 else 24))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 21 else 43) else (if i.val < 227 then 70 else 43)) else (if i.val < 230 then (if i.val < 229 then 68 else 41) else (if i.val < 231 then 21 else 40))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 73 else 38) else (if i.val < 235 then 71 else 41)) else (if i.val < 238 then (if i.val < 237 then 24 else 43) else (if i.val < 239 then 71 else 22)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 19 else 69) else (if i.val < 243 then 72 else 38)) else (if i.val < 246 then (if i.val < 245 then 43 else 20) else (if i.val < 247 then 38 else 72))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 40 else 68) else (if i.val < 251 then 38 else 73)) else (if i.val < 254 then (if i.val < 253 then 39 else 24) else (if i.val < 255 then 38 else 39))))))))

theorem g32p_supplierForest_actual_021 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_021 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_021 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_044941
  · exact g32p_supplierForest_actual_044962
  · exact g32p_supplierForest_actual_044972
  · exact g32p_supplierForest_actual_044986
  · exact g32p_supplierForest_actual_045005
  · exact g32p_supplierForest_actual_045084
  · exact g32p_supplierForest_actual_045092
  · exact g32p_supplierForest_actual_045124
  · exact g32p_supplierForest_actual_045140
  · exact g32p_supplierForest_actual_045155
  · exact g32p_supplierForest_actual_045167
  · exact g32p_supplierForest_actual_045169
  · exact g32p_supplierForest_actual_045191
  · exact g32p_supplierForest_actual_045195
  · exact g32p_supplierForest_actual_045286
  · exact g32p_supplierForest_actual_045294
  · exact g32p_supplierForest_actual_045334
  · exact g32p_supplierForest_actual_045341
  · exact g32p_supplierForest_actual_045370
  · exact g32p_supplierForest_actual_045398
  · exact g32p_supplierForest_actual_045433
  · exact g32p_supplierForest_actual_045475
  · exact g32p_supplierForest_actual_045477
  · exact g32p_supplierForest_actual_045566
  · exact g32p_supplierForest_actual_045598
  · exact g32p_supplierForest_actual_045629
  · exact g32p_supplierForest_actual_045639
  · exact g32p_supplierForest_actual_045705
  · exact g32p_supplierForest_actual_045786
  · exact g32p_supplierForest_actual_045813
  · exact g32p_supplierForest_actual_045883
  · exact g32p_supplierForest_actual_045894
  · exact g32p_supplierForest_actual_045959
  · exact g32p_supplierForest_actual_045971
  · exact g32p_supplierForest_actual_045975
  · exact g32p_supplierForest_actual_045976
  · exact g32p_supplierForest_actual_046061
  · exact g32p_supplierForest_actual_046079
  · exact g32p_supplierForest_actual_046104
  · exact g32p_supplierForest_actual_046106
  · exact g32p_supplierForest_actual_046156
  · exact g32p_supplierForest_actual_046161
  · exact g32p_supplierForest_actual_046177
  · exact g32p_supplierForest_actual_046183
  · exact g32p_supplierForest_actual_046202
  · exact g32p_supplierForest_actual_046209
  · exact g32p_supplierForest_actual_046230
  · exact g32p_supplierForest_actual_046250
  · exact g32p_supplierForest_actual_046255
  · exact g32p_supplierForest_actual_046261
  · exact g32p_supplierForest_actual_046347
  · exact g32p_supplierForest_actual_046421
  · exact g32p_supplierForest_actual_046425
  · exact g32p_supplierForest_actual_046449
  · exact g32p_supplierForest_actual_046461
  · exact g32p_supplierForest_actual_046481
  · exact g32p_supplierForest_actual_046495
  · exact g32p_supplierForest_actual_046589
  · exact g32p_supplierForest_actual_046597
  · exact g32p_supplierForest_actual_046625
  · exact g32p_supplierForest_actual_046639
  · exact g32p_supplierForest_actual_046660
  · exact g32p_supplierForest_actual_046684
  · exact g32p_supplierForest_actual_046693
  · exact g32p_supplierForest_actual_046753
  · exact g32p_supplierForest_actual_046755
  · exact g32p_supplierForest_actual_046756
  · exact g32p_supplierForest_actual_046779
  · exact g32p_supplierForest_actual_046790
  · exact g32p_supplierForest_actual_046799
  · exact g32p_supplierForest_actual_046901
  · exact g32p_supplierForest_actual_046970
  · exact g32p_supplierForest_actual_046973
  · exact g32p_supplierForest_actual_046991
  · exact g32p_supplierForest_actual_047022
  · exact g32p_supplierForest_actual_047052
  · exact g32p_supplierForest_actual_047059
  · exact g32p_supplierForest_actual_047063
  · exact g32p_supplierForest_actual_047070
  · exact g32p_supplierForest_actual_047093
  · exact g32p_supplierForest_actual_047102
  · exact g32p_supplierForest_actual_047216
  · exact g32p_supplierForest_actual_047232
  · exact g32p_supplierForest_actual_047258
  · exact g32p_supplierForest_actual_047262
  · exact g32p_supplierForest_actual_047309
  · exact g32p_supplierForest_actual_047421
  · exact g32p_supplierForest_actual_047495
  · exact g32p_supplierForest_actual_047550
  · exact g32p_supplierForest_actual_047574
  · exact g32p_supplierForest_actual_047581
  · exact g32p_supplierForest_actual_047589
  · exact g32p_supplierForest_actual_047609
  · exact g32p_supplierForest_actual_047618
  · exact g32p_supplierForest_actual_047664
  · exact g32p_supplierForest_actual_047691
  · exact g32p_supplierForest_actual_047696
  · exact g32p_supplierForest_actual_047702
  · exact g32p_supplierForest_actual_047727
  · exact g32p_supplierForest_actual_047730
  · exact g32p_supplierForest_actual_047731
  · exact g32p_supplierForest_actual_047757
  · exact g32p_supplierForest_actual_047783
  · exact g32p_supplierForest_actual_047823
  · exact g32p_supplierForest_actual_047865
  · exact g32p_supplierForest_actual_047904
  · exact g32p_supplierForest_actual_047923
  · exact g32p_supplierForest_actual_047958
  · exact g32p_supplierForest_actual_047962
  · exact g32p_supplierForest_actual_047993
  · exact g32p_supplierForest_actual_048039
  · exact g32p_supplierForest_actual_048056
  · exact g32p_supplierForest_actual_048082
  · exact g32p_supplierForest_actual_048110
  · exact g32p_supplierForest_actual_048184
  · exact g32p_supplierForest_actual_048195
  · exact g32p_supplierForest_actual_048208
  · exact g32p_supplierForest_actual_048280
  · exact g32p_supplierForest_actual_048297
  · exact g32p_supplierForest_actual_048303
  · exact g32p_supplierForest_actual_048332
  · exact g32p_supplierForest_actual_048334
  · exact g32p_supplierForest_actual_048346
  · exact g32p_supplierForest_actual_048529
  · exact g32p_supplierForest_actual_048569
  · exact g32p_supplierForest_actual_048772
  · exact g32p_supplierForest_actual_048924
  · exact g32p_supplierForest_actual_048964
  · exact g32p_supplierForest_actual_049060
  · exact g32p_supplierForest_actual_049156
  · exact g32p_supplierForest_actual_049266
  · exact g32p_supplierForest_actual_049324
  · exact g32p_supplierForest_actual_049325
  · exact g32p_supplierForest_actual_049327
  · exact g32p_supplierForest_actual_049333
  · exact g32p_supplierForest_actual_049375
  · exact g32p_supplierForest_actual_049378
  · exact g32p_supplierForest_actual_049398
  · exact g32p_supplierForest_actual_049489
  · exact g32p_supplierForest_actual_049573
  · exact g32p_supplierForest_actual_049581
  · exact g32p_supplierForest_actual_049608
  · exact g32p_supplierForest_actual_049649
  · exact g32p_supplierForest_actual_049706
  · exact g32p_supplierForest_actual_049849
  · exact g32p_supplierForest_actual_049850
  · exact g32p_supplierForest_actual_049858
  · exact g32p_supplierForest_actual_049859
  · exact g32p_supplierForest_actual_049982
  · exact g32p_supplierForest_actual_050005
  · exact g32p_supplierForest_actual_050007
  · exact g32p_supplierForest_actual_050017
  · exact g32p_supplierForest_actual_050130
  · exact g32p_supplierForest_actual_050132
  · exact g32p_supplierForest_actual_050151
  · exact g32p_supplierForest_actual_050200
  · exact g32p_supplierForest_actual_050254
  · exact g32p_supplierForest_actual_050287
  · exact g32p_supplierForest_actual_050378
  · exact g32p_supplierForest_actual_050520
  · exact g32p_supplierForest_actual_050544
  · exact g32p_supplierForest_actual_050585
  · exact g32p_supplierForest_actual_050672
  · exact g32p_supplierForest_actual_050687
  · exact g32p_supplierForest_actual_050702
  · exact g32p_supplierForest_actual_050703
  · exact g32p_supplierForest_actual_050728
  · exact g32p_supplierForest_actual_050798
  · exact g32p_supplierForest_actual_050854
  · exact g32p_supplierForest_actual_050891
  · exact g32p_supplierForest_actual_050929
  · exact g32p_supplierForest_actual_050977
  · exact g32p_supplierForest_actual_050997
  · exact g32p_supplierForest_actual_051059
  · exact g32p_supplierForest_actual_051068
  · exact g32p_supplierForest_actual_051071
  · exact g32p_supplierForest_actual_051094
  · exact g32p_supplierForest_actual_051139
  · exact g32p_supplierForest_actual_051144
  · exact g32p_supplierForest_actual_051150
  · exact g32p_supplierForest_actual_051163
  · exact g32p_supplierForest_actual_051164
  · exact g32p_supplierForest_actual_051190
  · exact g32p_supplierForest_actual_051212
  · exact g32p_supplierForest_actual_051240
  · exact g32p_supplierForest_actual_051304
  · exact g32p_supplierForest_actual_051337
  · exact g32p_supplierForest_actual_051430
  · exact g32p_supplierForest_actual_051456
  · exact g32p_supplierForest_actual_051483
  · exact g32p_supplierForest_actual_051484
  · exact g32p_supplierForest_actual_051507
  · exact g32p_supplierForest_actual_051543
  · exact g32p_supplierForest_actual_051635
  · exact g32p_supplierForest_actual_051642
  · exact g32p_supplierForest_actual_051715
  · exact g32p_supplierForest_actual_051780
  · exact g32p_supplierForest_actual_051811
  · exact g32p_supplierForest_actual_051818
  · exact g32p_supplierForest_actual_051869
  · exact g32p_supplierForest_actual_051905
  · exact g32p_supplierForest_actual_051910
  · exact g32p_supplierForest_actual_051957
  · exact g32p_supplierForest_actual_051983
  · exact g32p_supplierForest_actual_052007
  · exact g32p_supplierForest_actual_052017
  · exact g32p_supplierForest_actual_052021
  · exact g32p_supplierForest_actual_052027
  · exact g32p_supplierForest_actual_052028
  · exact g32p_supplierForest_actual_052160
  · exact g32p_supplierForest_actual_052184
  · exact g32p_supplierForest_actual_052195
  · exact g32p_supplierForest_actual_052206
  · exact g32p_supplierForest_actual_052238
  · exact g32p_supplierForest_actual_052317
  · exact g32p_supplierForest_actual_052334
  · exact g32p_supplierForest_actual_052352
  · exact g32p_supplierForest_actual_052411
  · exact g32p_supplierForest_actual_052433
  · exact g32p_supplierForest_actual_052632
  · exact g32p_supplierForest_actual_052647
  · exact g32p_supplierForest_actual_052805
  · exact g32p_supplierForest_actual_052819
  · exact g32p_supplierForest_actual_052844
  · exact g32p_supplierForest_actual_052846
  · exact g32p_supplierForest_actual_052911
  · exact g32p_supplierForest_actual_052965
  · exact g32p_supplierForest_actual_052997
  · exact g32p_supplierForest_actual_053002
  · exact g32p_supplierForest_actual_053024
  · exact g32p_supplierForest_actual_053043
  · exact g32p_supplierForest_actual_053057
  · exact g32p_supplierForest_actual_053060
  · exact g32p_supplierForest_actual_053094
  · exact g32p_supplierForest_actual_053098
  · exact g32p_supplierForest_actual_053122
  · exact g32p_supplierForest_actual_053180
  · exact g32p_supplierForest_actual_053198
  · exact g32p_supplierForest_actual_053200
  · exact g32p_supplierForest_actual_053213
  · exact g32p_supplierForest_actual_053240
  · exact g32p_supplierForest_actual_053312
  · exact g32p_supplierForest_actual_053339
  · exact g32p_supplierForest_actual_053403
  · exact g32p_supplierForest_actual_053422
  · exact g32p_supplierForest_actual_053488
  · exact g32p_supplierForest_actual_053515
  · exact g32p_supplierForest_actual_053528
  · exact g32p_supplierForest_actual_053577
  · exact g32p_supplierForest_actual_053601
  · exact g32p_supplierForest_actual_053607
  · exact g32p_supplierForest_actual_053618
  · exact g32p_supplierForest_actual_053628
  · exact g32p_supplierForest_actual_053645
  · exact g32p_supplierForest_actual_053701
  · exact g32p_supplierForest_actual_053751

def g32p_supplierForest_nodes_022 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_053807 else g32p_supplierForest_node_053823) else (if i.val < 3 then g32p_supplierForest_node_053905 else g32p_supplierForest_node_053922)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_053976 else g32p_supplierForest_node_053979) else (if i.val < 7 then g32p_supplierForest_node_054058 else g32p_supplierForest_node_054069))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_054109 else g32p_supplierForest_node_054153) else (if i.val < 11 then g32p_supplierForest_node_054170 else g32p_supplierForest_node_054223)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_054280 else g32p_supplierForest_node_054283) else (if i.val < 15 then g32p_supplierForest_node_054345 else g32p_supplierForest_node_054365)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_054367 else g32p_supplierForest_node_054378) else (if i.val < 19 then g32p_supplierForest_node_054379 else g32p_supplierForest_node_054481)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_054486 else g32p_supplierForest_node_054501) else (if i.val < 23 then g32p_supplierForest_node_054596 else g32p_supplierForest_node_054601))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_054664 else g32p_supplierForest_node_054725) else (if i.val < 27 then g32p_supplierForest_node_054735 else g32p_supplierForest_node_054779)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_054845 else g32p_supplierForest_node_054871) else (if i.val < 31 then g32p_supplierForest_node_054925 else g32p_supplierForest_node_054976))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_054998 else g32p_supplierForest_node_055047) else (if i.val < 35 then g32p_supplierForest_node_055060 else g32p_supplierForest_node_055112)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_055159 else g32p_supplierForest_node_055167) else (if i.val < 39 then g32p_supplierForest_node_055177 else g32p_supplierForest_node_055185))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_055196 else g32p_supplierForest_node_055214) else (if i.val < 43 then g32p_supplierForest_node_055290 else g32p_supplierForest_node_055341)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_055539 else g32p_supplierForest_node_055694) else (if i.val < 47 then g32p_supplierForest_node_055717 else g32p_supplierForest_node_055786)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_055837 else g32p_supplierForest_node_055936) else (if i.val < 51 then g32p_supplierForest_node_056001 else g32p_supplierForest_node_056031)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_056039 else g32p_supplierForest_node_056086) else (if i.val < 55 then g32p_supplierForest_node_056101 else g32p_supplierForest_node_056125))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_056147 else g32p_supplierForest_node_056326) else (if i.val < 59 then g32p_supplierForest_node_056342 else g32p_supplierForest_node_056359)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_056361 else g32p_supplierForest_node_056364) else (if i.val < 63 then g32p_supplierForest_node_056389 else g32p_supplierForest_node_056423)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_056556 else g32p_supplierForest_node_056588) else (if i.val < 67 then g32p_supplierForest_node_056681 else g32p_supplierForest_node_056713)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_056729 else g32p_supplierForest_node_056755) else (if i.val < 71 then g32p_supplierForest_node_056835 else g32p_supplierForest_node_056876))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_056905 else g32p_supplierForest_node_056933) else (if i.val < 75 then g32p_supplierForest_node_056944 else g32p_supplierForest_node_056987)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_056998 else g32p_supplierForest_node_057005) else (if i.val < 79 then g32p_supplierForest_node_057098 else g32p_supplierForest_node_057128)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_057174 else g32p_supplierForest_node_057177) else (if i.val < 83 then g32p_supplierForest_node_057196 else g32p_supplierForest_node_057201)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_057227 else g32p_supplierForest_node_057231) else (if i.val < 87 then g32p_supplierForest_node_057244 else g32p_supplierForest_node_057261))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_057281 else g32p_supplierForest_node_057284) else (if i.val < 91 then g32p_supplierForest_node_057367 else g32p_supplierForest_node_057373)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_057392 else g32p_supplierForest_node_057393) else (if i.val < 95 then g32p_supplierForest_node_057394 else g32p_supplierForest_node_057395))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_057406 else g32p_supplierForest_node_057453) else (if i.val < 99 then g32p_supplierForest_node_057495 else g32p_supplierForest_node_057507)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_057515 else g32p_supplierForest_node_057551) else (if i.val < 103 then g32p_supplierForest_node_057608 else g32p_supplierForest_node_057625))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_057683 else g32p_supplierForest_node_057686) else (if i.val < 107 then g32p_supplierForest_node_057687 else g32p_supplierForest_node_057729)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_057733 else g32p_supplierForest_node_057800) else (if i.val < 111 then g32p_supplierForest_node_057852 else g32p_supplierForest_node_057908)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_057920 else g32p_supplierForest_node_057938) else (if i.val < 115 then g32p_supplierForest_node_057966 else g32p_supplierForest_node_058050)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_058099 else g32p_supplierForest_node_058212) else (if i.val < 119 then g32p_supplierForest_node_058235 else g32p_supplierForest_node_058418))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_058436 else g32p_supplierForest_node_058511) else (if i.val < 123 then g32p_supplierForest_node_058534 else g32p_supplierForest_node_058544)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_058638 else g32p_supplierForest_node_058672) else (if i.val < 127 then g32p_supplierForest_node_058704 else g32p_supplierForest_node_058741))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_058785 else g32p_supplierForest_node_058790) else (if i.val < 131 then g32p_supplierForest_node_058810 else g32p_supplierForest_node_058932)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_058959 else g32p_supplierForest_node_059045) else (if i.val < 135 then g32p_supplierForest_node_059089 else g32p_supplierForest_node_059160))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_059218 else g32p_supplierForest_node_059268) else (if i.val < 139 then g32p_supplierForest_node_059309 else g32p_supplierForest_node_059319)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_059363 else g32p_supplierForest_node_059372) else (if i.val < 143 then g32p_supplierForest_node_059479 else g32p_supplierForest_node_059508)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_059548 else g32p_supplierForest_node_059551) else (if i.val < 147 then g32p_supplierForest_node_059572 else g32p_supplierForest_node_059620)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_059649 else g32p_supplierForest_node_059662) else (if i.val < 151 then g32p_supplierForest_node_059697 else g32p_supplierForest_node_059773))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_059807 else g32p_supplierForest_node_059814) else (if i.val < 155 then g32p_supplierForest_node_059922 else g32p_supplierForest_node_059950)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_059975 else g32p_supplierForest_node_059983) else (if i.val < 159 then g32p_supplierForest_node_060053 else g32p_supplierForest_node_060064))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_060167 else g32p_supplierForest_node_060174) else (if i.val < 163 then g32p_supplierForest_node_060279 else g32p_supplierForest_node_060305)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_060330 else g32p_supplierForest_node_060357) else (if i.val < 167 then g32p_supplierForest_node_060412 else g32p_supplierForest_node_060431))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_060441 else g32p_supplierForest_node_060451) else (if i.val < 171 then g32p_supplierForest_node_060490 else g32p_supplierForest_node_060507)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_060636 else g32p_supplierForest_node_060696) else (if i.val < 175 then g32p_supplierForest_node_060725 else g32p_supplierForest_node_060812)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_060830 else g32p_supplierForest_node_060895) else (if i.val < 179 then g32p_supplierForest_node_060942 else g32p_supplierForest_node_061012)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_061065 else g32p_supplierForest_node_061091) else (if i.val < 183 then g32p_supplierForest_node_061097 else g32p_supplierForest_node_061134))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_061139 else g32p_supplierForest_node_061259) else (if i.val < 187 then g32p_supplierForest_node_061274 else g32p_supplierForest_node_061279)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_061319 else g32p_supplierForest_node_061378) else (if i.val < 191 then g32p_supplierForest_node_061404 else g32p_supplierForest_node_061462)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_061465 else g32p_supplierForest_node_061511) else (if i.val < 195 then g32p_supplierForest_node_061527 else g32p_supplierForest_node_061536)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_061589 else g32p_supplierForest_node_061604) else (if i.val < 199 then g32p_supplierForest_node_061723 else g32p_supplierForest_node_061770))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_061813 else g32p_supplierForest_node_061830) else (if i.val < 203 then g32p_supplierForest_node_061866 else g32p_supplierForest_node_061875)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_061929 else g32p_supplierForest_node_062011) else (if i.val < 207 then g32p_supplierForest_node_062181 else g32p_supplierForest_node_062183)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_062194 else g32p_supplierForest_node_062204) else (if i.val < 211 then g32p_supplierForest_node_062209 else g32p_supplierForest_node_062240)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_062289 else g32p_supplierForest_node_062309) else (if i.val < 215 then g32p_supplierForest_node_062312 else g32p_supplierForest_node_062424))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_062426 else g32p_supplierForest_node_062462) else (if i.val < 219 then g32p_supplierForest_node_062549 else g32p_supplierForest_node_062619)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_062690 else g32p_supplierForest_node_062762) else (if i.val < 223 then g32p_supplierForest_node_062763 else g32p_supplierForest_node_062811))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_062872 else g32p_supplierForest_node_062908) else (if i.val < 227 then g32p_supplierForest_node_062915 else g32p_supplierForest_node_062916)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_063037 else g32p_supplierForest_node_063047) else (if i.val < 231 then g32p_supplierForest_node_063049 else g32p_supplierForest_node_063064))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_063077 else g32p_supplierForest_node_063097) else (if i.val < 235 then g32p_supplierForest_node_063116 else g32p_supplierForest_node_063122)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_063162 else g32p_supplierForest_node_063169) else (if i.val < 239 then g32p_supplierForest_node_063233 else g32p_supplierForest_node_063260)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_063306 else g32p_supplierForest_node_063325) else (if i.val < 243 then g32p_supplierForest_node_063349 else g32p_supplierForest_node_063354)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_063355 else g32p_supplierForest_node_063368) else (if i.val < 247 then g32p_supplierForest_node_063401 else g32p_supplierForest_node_063411))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_063540 else g32p_supplierForest_node_063578) else (if i.val < 251 then g32p_supplierForest_node_063590 else g32p_supplierForest_node_063610)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_063670 else g32p_supplierForest_node_063708) else (if i.val < 255 then g32p_supplierForest_node_063721 else g32p_supplierForest_node_063730))))))))

def g32p_supplierForest_classes_022 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 20 else 21) else (if i.val < 3 then 38 else 39)) else (if i.val < 6 then (if i.val < 5 then 21 else 38) else (if i.val < 7 then 6 else 75))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 39 else 67) else (if i.val < 11 then 74 else 69)) else (if i.val < 14 then (if i.val < 13 then 38 else 44) else (if i.val < 15 then 71 else 23)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 69 else 42) else (if i.val < 19 then 70 else 22)) else (if i.val < 22 then (if i.val < 21 then 69 else 43) else (if i.val < 23 then 72 else 74))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 70 else 67) else (if i.val < 27 then 21 else 70)) else (if i.val < 30 then (if i.val < 29 then 67 else 40) else (if i.val < 31 then 70 else 41))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 42) else (if i.val < 35 then 6 else 38)) else (if i.val < 38 then (if i.val < 37 then 68 else 74) else (if i.val < 39 then 39 else 73))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 22 else 38) else (if i.val < 43 then 21 else 75)) else (if i.val < 46 then (if i.val < 45 then 69 else 22) else (if i.val < 47 then 7 else 71)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 69 else 38) else (if i.val < 51 then 69 else 69)) else (if i.val < 54 then (if i.val < 53 then 40 else 68) else (if i.val < 55 then 69 else 74))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 69 else 73) else (if i.val < 59 then 68 else 6)) else (if i.val < 62 then (if i.val < 61 then 70 else 39) else (if i.val < 63 then 43 else 74)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 22 else 40) else (if i.val < 67 then 40 else 38)) else (if i.val < 70 then (if i.val < 69 then 74 else 74) else (if i.val < 71 then 38 else 21))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 70 else 21) else (if i.val < 75 then 38 else 70)) else (if i.val < 78 then (if i.val < 77 then 41 else 69) else (if i.val < 79 then 22 else 21)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 75 else 69) else (if i.val < 83 then 40 else 38)) else (if i.val < 86 then (if i.val < 85 then 67 else 75) else (if i.val < 87 then 74 else 74))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 20 else 21) else (if i.val < 91 then 21 else 69)) else (if i.val < 94 then (if i.val < 93 then 79 else 43) else (if i.val < 95 then 43 else 79))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 40 else 69) else (if i.val < 99 then 68 else 74)) else (if i.val < 102 then (if i.val < 101 then 75 else 69) else (if i.val < 103 then 38 else 69))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 41 else 69) else (if i.val < 107 then 71 else 68)) else (if i.val < 110 then (if i.val < 109 then 69 else 71) else (if i.val < 111 then 40 else 43)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 78 else 40) else (if i.val < 115 then 68 else 74)) else (if i.val < 118 then (if i.val < 117 then 40 else 22) else (if i.val < 119 then 21 else 43))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 21 else 75) else (if i.val < 123 then 69 else 42)) else (if i.val < 126 then (if i.val < 125 then 75 else 75) else (if i.val < 127 then 69 else 43))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 69 else 75) else (if i.val < 131 then 73 else 75)) else (if i.val < 134 then (if i.val < 133 then 22 else 74) else (if i.val < 135 then 21 else 21))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 43 else 7) else (if i.val < 139 then 22 else 38)) else (if i.val < 142 then (if i.val < 141 then 21 else 20) else (if i.val < 143 then 75 else 20)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 69 else 41) else (if i.val < 147 then 78 else 42)) else (if i.val < 150 then (if i.val < 149 then 43 else 23) else (if i.val < 151 then 69 else 69))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 69 else 75) else (if i.val < 155 then 38 else 40)) else (if i.val < 158 then (if i.val < 157 then 77 else 23) else (if i.val < 159 then 20 else 75))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 41 else 72) else (if i.val < 163 then 39 else 22)) else (if i.val < 166 then (if i.val < 165 then 24 else 43) else (if i.val < 167 then 74 else 41))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 71 else 43) else (if i.val < 171 then 39 else 74)) else (if i.val < 174 then (if i.val < 173 then 74 else 38) else (if i.val < 175 then 21 else 20)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 69) else (if i.val < 179 then 70 else 40)) else (if i.val < 182 then (if i.val < 181 then 74 else 72) else (if i.val < 183 then 70 else 70))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 71 else 71) else (if i.val < 187 then 70 else 69)) else (if i.val < 190 then (if i.val < 189 then 74 else 73) else (if i.val < 191 then 43 else 42)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 23 else 42) else (if i.val < 195 then 43 else 40)) else (if i.val < 198 then (if i.val < 197 then 41 else 43) else (if i.val < 199 then 6 else 43))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 75 else 21) else (if i.val < 203 then 40 else 41)) else (if i.val < 206 then (if i.val < 205 then 79 else 75) else (if i.val < 207 then 39 else 43)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 38 else 74) else (if i.val < 211 then 75 else 40)) else (if i.val < 214 then (if i.val < 213 then 43 else 6) else (if i.val < 215 then 21 else 22))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 38 else 43) else (if i.val < 219 then 41 else 38)) else (if i.val < 222 then (if i.val < 221 then 74 else 38) else (if i.val < 223 then 72 else 20))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 20 else 42) else (if i.val < 227 then 41 else 43)) else (if i.val < 230 then (if i.val < 229 then 40 else 22) else (if i.val < 231 then 70 else 23))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 70 else 23) else (if i.val < 235 then 18 else 18)) else (if i.val < 238 then (if i.val < 237 then 43 else 43) else (if i.val < 239 then 23 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 21 else 74) else (if i.val < 243 then 68 else 78)) else (if i.val < 246 then (if i.val < 245 then 68 else 68) else (if i.val < 247 then 73 else 6))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 72 else 41) else (if i.val < 251 then 39 else 40)) else (if i.val < 254 then (if i.val < 253 then 22 else 24) else (if i.val < 255 then 42 else 38))))))))

theorem g32p_supplierForest_actual_022 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_022 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_022 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_053807
  · exact g32p_supplierForest_actual_053823
  · exact g32p_supplierForest_actual_053905
  · exact g32p_supplierForest_actual_053922
  · exact g32p_supplierForest_actual_053976
  · exact g32p_supplierForest_actual_053979
  · exact g32p_supplierForest_actual_054058
  · exact g32p_supplierForest_actual_054069
  · exact g32p_supplierForest_actual_054109
  · exact g32p_supplierForest_actual_054153
  · exact g32p_supplierForest_actual_054170
  · exact g32p_supplierForest_actual_054223
  · exact g32p_supplierForest_actual_054280
  · exact g32p_supplierForest_actual_054283
  · exact g32p_supplierForest_actual_054345
  · exact g32p_supplierForest_actual_054365
  · exact g32p_supplierForest_actual_054367
  · exact g32p_supplierForest_actual_054378
  · exact g32p_supplierForest_actual_054379
  · exact g32p_supplierForest_actual_054481
  · exact g32p_supplierForest_actual_054486
  · exact g32p_supplierForest_actual_054501
  · exact g32p_supplierForest_actual_054596
  · exact g32p_supplierForest_actual_054601
  · exact g32p_supplierForest_actual_054664
  · exact g32p_supplierForest_actual_054725
  · exact g32p_supplierForest_actual_054735
  · exact g32p_supplierForest_actual_054779
  · exact g32p_supplierForest_actual_054845
  · exact g32p_supplierForest_actual_054871
  · exact g32p_supplierForest_actual_054925
  · exact g32p_supplierForest_actual_054976
  · exact g32p_supplierForest_actual_054998
  · exact g32p_supplierForest_actual_055047
  · exact g32p_supplierForest_actual_055060
  · exact g32p_supplierForest_actual_055112
  · exact g32p_supplierForest_actual_055159
  · exact g32p_supplierForest_actual_055167
  · exact g32p_supplierForest_actual_055177
  · exact g32p_supplierForest_actual_055185
  · exact g32p_supplierForest_actual_055196
  · exact g32p_supplierForest_actual_055214
  · exact g32p_supplierForest_actual_055290
  · exact g32p_supplierForest_actual_055341
  · exact g32p_supplierForest_actual_055539
  · exact g32p_supplierForest_actual_055694
  · exact g32p_supplierForest_actual_055717
  · exact g32p_supplierForest_actual_055786
  · exact g32p_supplierForest_actual_055837
  · exact g32p_supplierForest_actual_055936
  · exact g32p_supplierForest_actual_056001
  · exact g32p_supplierForest_actual_056031
  · exact g32p_supplierForest_actual_056039
  · exact g32p_supplierForest_actual_056086
  · exact g32p_supplierForest_actual_056101
  · exact g32p_supplierForest_actual_056125
  · exact g32p_supplierForest_actual_056147
  · exact g32p_supplierForest_actual_056326
  · exact g32p_supplierForest_actual_056342
  · exact g32p_supplierForest_actual_056359
  · exact g32p_supplierForest_actual_056361
  · exact g32p_supplierForest_actual_056364
  · exact g32p_supplierForest_actual_056389
  · exact g32p_supplierForest_actual_056423
  · exact g32p_supplierForest_actual_056556
  · exact g32p_supplierForest_actual_056588
  · exact g32p_supplierForest_actual_056681
  · exact g32p_supplierForest_actual_056713
  · exact g32p_supplierForest_actual_056729
  · exact g32p_supplierForest_actual_056755
  · exact g32p_supplierForest_actual_056835
  · exact g32p_supplierForest_actual_056876
  · exact g32p_supplierForest_actual_056905
  · exact g32p_supplierForest_actual_056933
  · exact g32p_supplierForest_actual_056944
  · exact g32p_supplierForest_actual_056987
  · exact g32p_supplierForest_actual_056998
  · exact g32p_supplierForest_actual_057005
  · exact g32p_supplierForest_actual_057098
  · exact g32p_supplierForest_actual_057128
  · exact g32p_supplierForest_actual_057174
  · exact g32p_supplierForest_actual_057177
  · exact g32p_supplierForest_actual_057196
  · exact g32p_supplierForest_actual_057201
  · exact g32p_supplierForest_actual_057227
  · exact g32p_supplierForest_actual_057231
  · exact g32p_supplierForest_actual_057244
  · exact g32p_supplierForest_actual_057261
  · exact g32p_supplierForest_actual_057281
  · exact g32p_supplierForest_actual_057284
  · exact g32p_supplierForest_actual_057367
  · exact g32p_supplierForest_actual_057373
  · exact g32p_supplierForest_actual_057392
  · exact g32p_supplierForest_actual_057393
  · exact g32p_supplierForest_actual_057394
  · exact g32p_supplierForest_actual_057395
  · exact g32p_supplierForest_actual_057406
  · exact g32p_supplierForest_actual_057453
  · exact g32p_supplierForest_actual_057495
  · exact g32p_supplierForest_actual_057507
  · exact g32p_supplierForest_actual_057515
  · exact g32p_supplierForest_actual_057551
  · exact g32p_supplierForest_actual_057608
  · exact g32p_supplierForest_actual_057625
  · exact g32p_supplierForest_actual_057683
  · exact g32p_supplierForest_actual_057686
  · exact g32p_supplierForest_actual_057687
  · exact g32p_supplierForest_actual_057729
  · exact g32p_supplierForest_actual_057733
  · exact g32p_supplierForest_actual_057800
  · exact g32p_supplierForest_actual_057852
  · exact g32p_supplierForest_actual_057908
  · exact g32p_supplierForest_actual_057920
  · exact g32p_supplierForest_actual_057938
  · exact g32p_supplierForest_actual_057966
  · exact g32p_supplierForest_actual_058050
  · exact g32p_supplierForest_actual_058099
  · exact g32p_supplierForest_actual_058212
  · exact g32p_supplierForest_actual_058235
  · exact g32p_supplierForest_actual_058418
  · exact g32p_supplierForest_actual_058436
  · exact g32p_supplierForest_actual_058511
  · exact g32p_supplierForest_actual_058534
  · exact g32p_supplierForest_actual_058544
  · exact g32p_supplierForest_actual_058638
  · exact g32p_supplierForest_actual_058672
  · exact g32p_supplierForest_actual_058704
  · exact g32p_supplierForest_actual_058741
  · exact g32p_supplierForest_actual_058785
  · exact g32p_supplierForest_actual_058790
  · exact g32p_supplierForest_actual_058810
  · exact g32p_supplierForest_actual_058932
  · exact g32p_supplierForest_actual_058959
  · exact g32p_supplierForest_actual_059045
  · exact g32p_supplierForest_actual_059089
  · exact g32p_supplierForest_actual_059160
  · exact g32p_supplierForest_actual_059218
  · exact g32p_supplierForest_actual_059268
  · exact g32p_supplierForest_actual_059309
  · exact g32p_supplierForest_actual_059319
  · exact g32p_supplierForest_actual_059363
  · exact g32p_supplierForest_actual_059372
  · exact g32p_supplierForest_actual_059479
  · exact g32p_supplierForest_actual_059508
  · exact g32p_supplierForest_actual_059548
  · exact g32p_supplierForest_actual_059551
  · exact g32p_supplierForest_actual_059572
  · exact g32p_supplierForest_actual_059620
  · exact g32p_supplierForest_actual_059649
  · exact g32p_supplierForest_actual_059662
  · exact g32p_supplierForest_actual_059697
  · exact g32p_supplierForest_actual_059773
  · exact g32p_supplierForest_actual_059807
  · exact g32p_supplierForest_actual_059814
  · exact g32p_supplierForest_actual_059922
  · exact g32p_supplierForest_actual_059950
  · exact g32p_supplierForest_actual_059975
  · exact g32p_supplierForest_actual_059983
  · exact g32p_supplierForest_actual_060053
  · exact g32p_supplierForest_actual_060064
  · exact g32p_supplierForest_actual_060167
  · exact g32p_supplierForest_actual_060174
  · exact g32p_supplierForest_actual_060279
  · exact g32p_supplierForest_actual_060305
  · exact g32p_supplierForest_actual_060330
  · exact g32p_supplierForest_actual_060357
  · exact g32p_supplierForest_actual_060412
  · exact g32p_supplierForest_actual_060431
  · exact g32p_supplierForest_actual_060441
  · exact g32p_supplierForest_actual_060451
  · exact g32p_supplierForest_actual_060490
  · exact g32p_supplierForest_actual_060507
  · exact g32p_supplierForest_actual_060636
  · exact g32p_supplierForest_actual_060696
  · exact g32p_supplierForest_actual_060725
  · exact g32p_supplierForest_actual_060812
  · exact g32p_supplierForest_actual_060830
  · exact g32p_supplierForest_actual_060895
  · exact g32p_supplierForest_actual_060942
  · exact g32p_supplierForest_actual_061012
  · exact g32p_supplierForest_actual_061065
  · exact g32p_supplierForest_actual_061091
  · exact g32p_supplierForest_actual_061097
  · exact g32p_supplierForest_actual_061134
  · exact g32p_supplierForest_actual_061139
  · exact g32p_supplierForest_actual_061259
  · exact g32p_supplierForest_actual_061274
  · exact g32p_supplierForest_actual_061279
  · exact g32p_supplierForest_actual_061319
  · exact g32p_supplierForest_actual_061378
  · exact g32p_supplierForest_actual_061404
  · exact g32p_supplierForest_actual_061462
  · exact g32p_supplierForest_actual_061465
  · exact g32p_supplierForest_actual_061511
  · exact g32p_supplierForest_actual_061527
  · exact g32p_supplierForest_actual_061536
  · exact g32p_supplierForest_actual_061589
  · exact g32p_supplierForest_actual_061604
  · exact g32p_supplierForest_actual_061723
  · exact g32p_supplierForest_actual_061770
  · exact g32p_supplierForest_actual_061813
  · exact g32p_supplierForest_actual_061830
  · exact g32p_supplierForest_actual_061866
  · exact g32p_supplierForest_actual_061875
  · exact g32p_supplierForest_actual_061929
  · exact g32p_supplierForest_actual_062011
  · exact g32p_supplierForest_actual_062181
  · exact g32p_supplierForest_actual_062183
  · exact g32p_supplierForest_actual_062194
  · exact g32p_supplierForest_actual_062204
  · exact g32p_supplierForest_actual_062209
  · exact g32p_supplierForest_actual_062240
  · exact g32p_supplierForest_actual_062289
  · exact g32p_supplierForest_actual_062309
  · exact g32p_supplierForest_actual_062312
  · exact g32p_supplierForest_actual_062424
  · exact g32p_supplierForest_actual_062426
  · exact g32p_supplierForest_actual_062462
  · exact g32p_supplierForest_actual_062549
  · exact g32p_supplierForest_actual_062619
  · exact g32p_supplierForest_actual_062690
  · exact g32p_supplierForest_actual_062762
  · exact g32p_supplierForest_actual_062763
  · exact g32p_supplierForest_actual_062811
  · exact g32p_supplierForest_actual_062872
  · exact g32p_supplierForest_actual_062908
  · exact g32p_supplierForest_actual_062915
  · exact g32p_supplierForest_actual_062916
  · exact g32p_supplierForest_actual_063037
  · exact g32p_supplierForest_actual_063047
  · exact g32p_supplierForest_actual_063049
  · exact g32p_supplierForest_actual_063064
  · exact g32p_supplierForest_actual_063077
  · exact g32p_supplierForest_actual_063097
  · exact g32p_supplierForest_actual_063116
  · exact g32p_supplierForest_actual_063122
  · exact g32p_supplierForest_actual_063162
  · exact g32p_supplierForest_actual_063169
  · exact g32p_supplierForest_actual_063233
  · exact g32p_supplierForest_actual_063260
  · exact g32p_supplierForest_actual_063306
  · exact g32p_supplierForest_actual_063325
  · exact g32p_supplierForest_actual_063349
  · exact g32p_supplierForest_actual_063354
  · exact g32p_supplierForest_actual_063355
  · exact g32p_supplierForest_actual_063368
  · exact g32p_supplierForest_actual_063401
  · exact g32p_supplierForest_actual_063411
  · exact g32p_supplierForest_actual_063540
  · exact g32p_supplierForest_actual_063578
  · exact g32p_supplierForest_actual_063590
  · exact g32p_supplierForest_actual_063610
  · exact g32p_supplierForest_actual_063670
  · exact g32p_supplierForest_actual_063708
  · exact g32p_supplierForest_actual_063721
  · exact g32p_supplierForest_actual_063730

def g32p_supplierForest_nodes_023 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_063756 else g32p_supplierForest_node_063852) else (if i.val < 3 then g32p_supplierForest_node_063882 else g32p_supplierForest_node_063894)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_063919 else g32p_supplierForest_node_063926) else (if i.val < 7 then g32p_supplierForest_node_064015 else g32p_supplierForest_node_064064))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_064080 else g32p_supplierForest_node_064115) else (if i.val < 11 then g32p_supplierForest_node_064143 else g32p_supplierForest_node_064206)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_064208 else g32p_supplierForest_node_064229) else (if i.val < 15 then g32p_supplierForest_node_064314 else g32p_supplierForest_node_064326)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_064418 else g32p_supplierForest_node_064429) else (if i.val < 19 then g32p_supplierForest_node_064474 else g32p_supplierForest_node_064478)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_064484 else g32p_supplierForest_node_064506) else (if i.val < 23 then g32p_supplierForest_node_064517 else g32p_supplierForest_node_064612))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_064637 else g32p_supplierForest_node_064861) else (if i.val < 27 then g32p_supplierForest_node_064862 else g32p_supplierForest_node_064883)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_064912 else g32p_supplierForest_node_064971) else (if i.val < 31 then g32p_supplierForest_node_064973 else g32p_supplierForest_node_065002))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_065062 else g32p_supplierForest_node_065079) else (if i.val < 35 then g32p_supplierForest_node_065187 else g32p_supplierForest_node_065212)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_065314 else g32p_supplierForest_node_065409) else (if i.val < 39 then g32p_supplierForest_node_065426 else g32p_supplierForest_node_065449))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_065515 else g32p_supplierForest_node_065626) else (if i.val < 43 then g32p_supplierForest_node_065627 else g32p_supplierForest_node_065658)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_065671 else g32p_supplierForest_node_065690) else (if i.val < 47 then g32p_supplierForest_node_065872 else g32p_supplierForest_node_065884)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_065924 else g32p_supplierForest_node_065936) else (if i.val < 51 then g32p_supplierForest_node_066132 else g32p_supplierForest_node_066146)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_066198 else g32p_supplierForest_node_066207) else (if i.val < 55 then g32p_supplierForest_node_066298 else g32p_supplierForest_node_066421))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_066431 else g32p_supplierForest_node_066444) else (if i.val < 59 then g32p_supplierForest_node_066471 else g32p_supplierForest_node_066593)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_066607 else g32p_supplierForest_node_066619) else (if i.val < 63 then g32p_supplierForest_node_066634 else g32p_supplierForest_node_066803)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_066829 else g32p_supplierForest_node_066847) else (if i.val < 67 then g32p_supplierForest_node_066923 else g32p_supplierForest_node_066950)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_067016 else g32p_supplierForest_node_067026) else (if i.val < 71 then g32p_supplierForest_node_067031 else g32p_supplierForest_node_067034))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_067040 else g32p_supplierForest_node_067061) else (if i.val < 75 then g32p_supplierForest_node_067089 else g32p_supplierForest_node_067103)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_067127 else g32p_supplierForest_node_067147) else (if i.val < 79 then g32p_supplierForest_node_067162 else g32p_supplierForest_node_067209)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_067246 else g32p_supplierForest_node_067297) else (if i.val < 83 then g32p_supplierForest_node_067302 else g32p_supplierForest_node_067325)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_067381 else g32p_supplierForest_node_067382) else (if i.val < 87 then g32p_supplierForest_node_067400 else g32p_supplierForest_node_067454))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_067565 else g32p_supplierForest_node_067572) else (if i.val < 91 then g32p_supplierForest_node_067689 else g32p_supplierForest_node_067698)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_067701 else g32p_supplierForest_node_067772) else (if i.val < 95 then g32p_supplierForest_node_067878 else g32p_supplierForest_node_067879))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_067885 else g32p_supplierForest_node_067906) else (if i.val < 99 then g32p_supplierForest_node_067935 else g32p_supplierForest_node_067973)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_067988 else g32p_supplierForest_node_068002) else (if i.val < 103 then g32p_supplierForest_node_068030 else g32p_supplierForest_node_068050))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_068151 else g32p_supplierForest_node_068152) else (if i.val < 107 then g32p_supplierForest_node_068164 else g32p_supplierForest_node_068220)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_068238 else g32p_supplierForest_node_068302) else (if i.val < 111 then g32p_supplierForest_node_068308 else g32p_supplierForest_node_068341)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_068343 else g32p_supplierForest_node_068383) else (if i.val < 115 then g32p_supplierForest_node_068403 else g32p_supplierForest_node_068404)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_068420 else g32p_supplierForest_node_068441) else (if i.val < 119 then g32p_supplierForest_node_068449 else g32p_supplierForest_node_068514))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_068522 else g32p_supplierForest_node_068553) else (if i.val < 123 then g32p_supplierForest_node_068580 else g32p_supplierForest_node_068583)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_068611 else g32p_supplierForest_node_068733) else (if i.val < 127 then g32p_supplierForest_node_068778 else g32p_supplierForest_node_068781))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_068807 else g32p_supplierForest_node_068841) else (if i.val < 131 then g32p_supplierForest_node_068854 else g32p_supplierForest_node_068909)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_068937 else g32p_supplierForest_node_068941) else (if i.val < 135 then g32p_supplierForest_node_068962 else g32p_supplierForest_node_068968))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_068972 else g32p_supplierForest_node_069044) else (if i.val < 139 then g32p_supplierForest_node_069076 else g32p_supplierForest_node_069094)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_069101 else g32p_supplierForest_node_069139) else (if i.val < 143 then g32p_supplierForest_node_069147 else g32p_supplierForest_node_069160)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_069168 else g32p_supplierForest_node_069257) else (if i.val < 147 then g32p_supplierForest_node_069364 else g32p_supplierForest_node_069373)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_069392 else g32p_supplierForest_node_069461) else (if i.val < 151 then g32p_supplierForest_node_069487 else g32p_supplierForest_node_069574))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_069688 else g32p_supplierForest_node_069710) else (if i.val < 155 then g32p_supplierForest_node_069717 else g32p_supplierForest_node_069722)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_069744 else g32p_supplierForest_node_069770) else (if i.val < 159 then g32p_supplierForest_node_069858 else g32p_supplierForest_node_069905))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_069939 else g32p_supplierForest_node_069982) else (if i.val < 163 then g32p_supplierForest_node_069985 else g32p_supplierForest_node_069989)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_070012 else g32p_supplierForest_node_070056) else (if i.val < 167 then g32p_supplierForest_node_070096 else g32p_supplierForest_node_070115))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_070134 else g32p_supplierForest_node_070150) else (if i.val < 171 then g32p_supplierForest_node_070199 else g32p_supplierForest_node_070236)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_070248 else g32p_supplierForest_node_070324) else (if i.val < 175 then g32p_supplierForest_node_070338 else g32p_supplierForest_node_070392)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_070404 else g32p_supplierForest_node_070428) else (if i.val < 179 then g32p_supplierForest_node_070430 else g32p_supplierForest_node_070467)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_070578 else g32p_supplierForest_node_070597) else (if i.val < 183 then g32p_supplierForest_node_070602 else g32p_supplierForest_node_070749))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_070763 else g32p_supplierForest_node_070780) else (if i.val < 187 then g32p_supplierForest_node_070785 else g32p_supplierForest_node_070879)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_070909 else g32p_supplierForest_node_070961) else (if i.val < 191 then g32p_supplierForest_node_071157 else g32p_supplierForest_node_071167)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_071172 else g32p_supplierForest_node_071181) else (if i.val < 195 then g32p_supplierForest_node_071191 else g32p_supplierForest_node_071194)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_071203 else g32p_supplierForest_node_071257) else (if i.val < 199 then g32p_supplierForest_node_071306 else g32p_supplierForest_node_071309))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_071339 else g32p_supplierForest_node_071398) else (if i.val < 203 then g32p_supplierForest_node_071399 else g32p_supplierForest_node_071413)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_071427 else g32p_supplierForest_node_071462) else (if i.val < 207 then g32p_supplierForest_node_071463 else g32p_supplierForest_node_071467)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_071494 else g32p_supplierForest_node_071495) else (if i.val < 211 then g32p_supplierForest_node_071504 else g32p_supplierForest_node_071570)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_071612 else g32p_supplierForest_node_071623) else (if i.val < 215 then g32p_supplierForest_node_071753 else g32p_supplierForest_node_071762))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_071785 else g32p_supplierForest_node_071791) else (if i.val < 219 then g32p_supplierForest_node_071811 else g32p_supplierForest_node_071822)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_071835 else g32p_supplierForest_node_071913) else (if i.val < 223 then g32p_supplierForest_node_071914 else g32p_supplierForest_node_072012))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_072037 else g32p_supplierForest_node_072041) else (if i.val < 227 then g32p_supplierForest_node_072113 else g32p_supplierForest_node_072145)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_072206 else g32p_supplierForest_node_072209) else (if i.val < 231 then g32p_supplierForest_node_072335 else g32p_supplierForest_node_072375))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_072403 else g32p_supplierForest_node_072411) else (if i.val < 235 then g32p_supplierForest_node_072517 else g32p_supplierForest_node_072523)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_072612 else g32p_supplierForest_node_072616) else (if i.val < 239 then g32p_supplierForest_node_072617 else g32p_supplierForest_node_072632)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_072662 else g32p_supplierForest_node_072687) else (if i.val < 243 then g32p_supplierForest_node_072719 else g32p_supplierForest_node_072724)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_072738 else g32p_supplierForest_node_072802) else (if i.val < 247 then g32p_supplierForest_node_072805 else g32p_supplierForest_node_072814))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_072820 else g32p_supplierForest_node_072823) else (if i.val < 251 then g32p_supplierForest_node_072885 else g32p_supplierForest_node_072902)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_072921 else g32p_supplierForest_node_073002) else (if i.val < 255 then g32p_supplierForest_node_073140 else g32p_supplierForest_node_073155))))))))

def g32p_supplierForest_classes_023 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 69 else 6) else (if i.val < 3 then 38 else 43)) else (if i.val < 6 then (if i.val < 5 then 6 else 20) else (if i.val < 7 then 21 else 21))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 24 else 38) else (if i.val < 11 then 21 else 22)) else (if i.val < 14 then (if i.val < 13 then 6 else 21) else (if i.val < 15 then 38 else 43)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 5 else 20) else (if i.val < 19 then 21 else 40)) else (if i.val < 22 then (if i.val < 21 then 21 else 21) else (if i.val < 23 then 69 else 40))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 69 else 22) else (if i.val < 27 then 21 else 23)) else (if i.val < 30 then (if i.val < 29 then 23 else 73) else (if i.val < 31 then 21 else 38))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 74 else 69) else (if i.val < 35 then 69 else 41)) else (if i.val < 38 then (if i.val < 37 then 38 else 43) else (if i.val < 39 then 69 else 69))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 7 else 24) else (if i.val < 43 then 43 else 41)) else (if i.val < 46 then (if i.val < 45 then 21 else 21) else (if i.val < 47 then 6 else 42)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 69 else 6) else (if i.val < 51 then 21 else 41)) else (if i.val < 54 then (if i.val < 53 then 42 else 69) else (if i.val < 55 then 6 else 21))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 74) else (if i.val < 59 then 72 else 69)) else (if i.val < 62 then (if i.val < 61 then 6 else 38) else (if i.val < 63 then 21 else 40)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 74 else 74) else (if i.val < 67 then 69 else 74)) else (if i.val < 70 then (if i.val < 69 then 79 else 69) else (if i.val < 71 then 72 else 20))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 69 else 69) else (if i.val < 75 then 20 else 40)) else (if i.val < 78 then (if i.val < 77 then 75 else 22) else (if i.val < 79 then 21 else 23)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 21 else 43) else (if i.val < 83 then 38 else 69)) else (if i.val < 86 then (if i.val < 85 then 72 else 68) else (if i.val < 87 then 38 else 71))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 74 else 68) else (if i.val < 91 then 74 else 40)) else (if i.val < 94 then (if i.val < 93 then 38 else 74) else (if i.val < 95 then 21 else 20))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 71 else 73) else (if i.val < 99 then 38 else 43)) else (if i.val < 102 then (if i.val < 101 then 69 else 41) else (if i.val < 103 then 71 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 69 else 73) else (if i.val < 107 then 75 else 74)) else (if i.val < 110 then (if i.val < 109 then 73 else 68) else (if i.val < 111 then 73 else 73)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 78 else 20) else (if i.val < 115 then 43 else 42)) else (if i.val < 118 then (if i.val < 117 then 42 else 69) else (if i.val < 119 then 68 else 74))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 73 else 38) else (if i.val < 123 then 75 else 21)) else (if i.val < 126 then (if i.val < 125 then 21 else 71) else (if i.val < 127 then 69 else 43))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 38 else 18) else (if i.val < 131 then 6 else 69)) else (if i.val < 134 then (if i.val < 133 then 22 else 18) else (if i.val < 135 then 23 else 43))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 22 else 68) else (if i.val < 139 then 73 else 21)) else (if i.val < 142 then (if i.val < 141 then 74 else 20) else (if i.val < 143 then 42 else 42)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 43 else 68) else (if i.val < 147 then 43 else 21)) else (if i.val < 150 then (if i.val < 149 then 6 else 42) else (if i.val < 151 then 42 else 75))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 38 else 73) else (if i.val < 155 then 69 else 21)) else (if i.val < 158 then (if i.val < 157 then 21 else 69) else (if i.val < 159 then 38 else 75))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 21 else 20) else (if i.val < 163 then 21 else 22)) else (if i.val < 166 then (if i.val < 165 then 38 else 41) else (if i.val < 167 then 79 else 70))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 74 else 70) else (if i.val < 171 then 20 else 69)) else (if i.val < 174 then (if i.val < 173 then 70 else 79) else (if i.val < 175 then 42 else 69)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 73 else 74) else (if i.val < 179 then 73 else 71)) else (if i.val < 182 then (if i.val < 181 then 21 else 73) else (if i.val < 183 then 20 else 75))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 69 else 74) else (if i.val < 187 then 73 else 75)) else (if i.val < 190 then (if i.val < 189 then 69 else 74) else (if i.val < 191 then 41 else 75)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 20 else 77) else (if i.val < 195 then 20 else 72)) else (if i.val < 198 then (if i.val < 197 then 6 else 21) else (if i.val < 199 then 22 else 38))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 21 else 41) else (if i.val < 203 then 38 else 18)) else (if i.val < 206 then (if i.val < 205 then 71 else 18) else (if i.val < 207 then 38 else 22)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 38 else 21) else (if i.val < 211 then 42 else 22)) else (if i.val < 214 then (if i.val < 213 then 39 else 72) else (if i.val < 215 then 25 else 47))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 9 else 56) else (if i.val < 219 then 26 else 53)) else (if i.val < 222 then (if i.val < 221 then 46 else 13) else (if i.val < 223 then 47 else 52))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 10 else 49) else (if i.val < 227 then 27 else 47)) else (if i.val < 230 then (if i.val < 229 then 83 else 26) else (if i.val < 231 then 13 else 47))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 52 else 52) else (if i.val < 235 then 50 else 53)) else (if i.val < 238 then (if i.val < 237 then 48 else 49) else (if i.val < 239 then 53 else 50)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 47) else (if i.val < 243 then 49 else 51)) else (if i.val < 246 then (if i.val < 245 then 49 else 10) else (if i.val < 247 then 26 else 50))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 80 else 49) else (if i.val < 251 then 50 else 49)) else (if i.val < 254 then (if i.val < 253 then 11 else 84) else (if i.val < 255 then 49 else 52))))))))

theorem g32p_supplierForest_actual_023 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_023 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_023 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_063756
  · exact g32p_supplierForest_actual_063852
  · exact g32p_supplierForest_actual_063882
  · exact g32p_supplierForest_actual_063894
  · exact g32p_supplierForest_actual_063919
  · exact g32p_supplierForest_actual_063926
  · exact g32p_supplierForest_actual_064015
  · exact g32p_supplierForest_actual_064064
  · exact g32p_supplierForest_actual_064080
  · exact g32p_supplierForest_actual_064115
  · exact g32p_supplierForest_actual_064143
  · exact g32p_supplierForest_actual_064206
  · exact g32p_supplierForest_actual_064208
  · exact g32p_supplierForest_actual_064229
  · exact g32p_supplierForest_actual_064314
  · exact g32p_supplierForest_actual_064326
  · exact g32p_supplierForest_actual_064418
  · exact g32p_supplierForest_actual_064429
  · exact g32p_supplierForest_actual_064474
  · exact g32p_supplierForest_actual_064478
  · exact g32p_supplierForest_actual_064484
  · exact g32p_supplierForest_actual_064506
  · exact g32p_supplierForest_actual_064517
  · exact g32p_supplierForest_actual_064612
  · exact g32p_supplierForest_actual_064637
  · exact g32p_supplierForest_actual_064861
  · exact g32p_supplierForest_actual_064862
  · exact g32p_supplierForest_actual_064883
  · exact g32p_supplierForest_actual_064912
  · exact g32p_supplierForest_actual_064971
  · exact g32p_supplierForest_actual_064973
  · exact g32p_supplierForest_actual_065002
  · exact g32p_supplierForest_actual_065062
  · exact g32p_supplierForest_actual_065079
  · exact g32p_supplierForest_actual_065187
  · exact g32p_supplierForest_actual_065212
  · exact g32p_supplierForest_actual_065314
  · exact g32p_supplierForest_actual_065409
  · exact g32p_supplierForest_actual_065426
  · exact g32p_supplierForest_actual_065449
  · exact g32p_supplierForest_actual_065515
  · exact g32p_supplierForest_actual_065626
  · exact g32p_supplierForest_actual_065627
  · exact g32p_supplierForest_actual_065658
  · exact g32p_supplierForest_actual_065671
  · exact g32p_supplierForest_actual_065690
  · exact g32p_supplierForest_actual_065872
  · exact g32p_supplierForest_actual_065884
  · exact g32p_supplierForest_actual_065924
  · exact g32p_supplierForest_actual_065936
  · exact g32p_supplierForest_actual_066132
  · exact g32p_supplierForest_actual_066146
  · exact g32p_supplierForest_actual_066198
  · exact g32p_supplierForest_actual_066207
  · exact g32p_supplierForest_actual_066298
  · exact g32p_supplierForest_actual_066421
  · exact g32p_supplierForest_actual_066431
  · exact g32p_supplierForest_actual_066444
  · exact g32p_supplierForest_actual_066471
  · exact g32p_supplierForest_actual_066593
  · exact g32p_supplierForest_actual_066607
  · exact g32p_supplierForest_actual_066619
  · exact g32p_supplierForest_actual_066634
  · exact g32p_supplierForest_actual_066803
  · exact g32p_supplierForest_actual_066829
  · exact g32p_supplierForest_actual_066847
  · exact g32p_supplierForest_actual_066923
  · exact g32p_supplierForest_actual_066950
  · exact g32p_supplierForest_actual_067016
  · exact g32p_supplierForest_actual_067026
  · exact g32p_supplierForest_actual_067031
  · exact g32p_supplierForest_actual_067034
  · exact g32p_supplierForest_actual_067040
  · exact g32p_supplierForest_actual_067061
  · exact g32p_supplierForest_actual_067089
  · exact g32p_supplierForest_actual_067103
  · exact g32p_supplierForest_actual_067127
  · exact g32p_supplierForest_actual_067147
  · exact g32p_supplierForest_actual_067162
  · exact g32p_supplierForest_actual_067209
  · exact g32p_supplierForest_actual_067246
  · exact g32p_supplierForest_actual_067297
  · exact g32p_supplierForest_actual_067302
  · exact g32p_supplierForest_actual_067325
  · exact g32p_supplierForest_actual_067381
  · exact g32p_supplierForest_actual_067382
  · exact g32p_supplierForest_actual_067400
  · exact g32p_supplierForest_actual_067454
  · exact g32p_supplierForest_actual_067565
  · exact g32p_supplierForest_actual_067572
  · exact g32p_supplierForest_actual_067689
  · exact g32p_supplierForest_actual_067698
  · exact g32p_supplierForest_actual_067701
  · exact g32p_supplierForest_actual_067772
  · exact g32p_supplierForest_actual_067878
  · exact g32p_supplierForest_actual_067879
  · exact g32p_supplierForest_actual_067885
  · exact g32p_supplierForest_actual_067906
  · exact g32p_supplierForest_actual_067935
  · exact g32p_supplierForest_actual_067973
  · exact g32p_supplierForest_actual_067988
  · exact g32p_supplierForest_actual_068002
  · exact g32p_supplierForest_actual_068030
  · exact g32p_supplierForest_actual_068050
  · exact g32p_supplierForest_actual_068151
  · exact g32p_supplierForest_actual_068152
  · exact g32p_supplierForest_actual_068164
  · exact g32p_supplierForest_actual_068220
  · exact g32p_supplierForest_actual_068238
  · exact g32p_supplierForest_actual_068302
  · exact g32p_supplierForest_actual_068308
  · exact g32p_supplierForest_actual_068341
  · exact g32p_supplierForest_actual_068343
  · exact g32p_supplierForest_actual_068383
  · exact g32p_supplierForest_actual_068403
  · exact g32p_supplierForest_actual_068404
  · exact g32p_supplierForest_actual_068420
  · exact g32p_supplierForest_actual_068441
  · exact g32p_supplierForest_actual_068449
  · exact g32p_supplierForest_actual_068514
  · exact g32p_supplierForest_actual_068522
  · exact g32p_supplierForest_actual_068553
  · exact g32p_supplierForest_actual_068580
  · exact g32p_supplierForest_actual_068583
  · exact g32p_supplierForest_actual_068611
  · exact g32p_supplierForest_actual_068733
  · exact g32p_supplierForest_actual_068778
  · exact g32p_supplierForest_actual_068781
  · exact g32p_supplierForest_actual_068807
  · exact g32p_supplierForest_actual_068841
  · exact g32p_supplierForest_actual_068854
  · exact g32p_supplierForest_actual_068909
  · exact g32p_supplierForest_actual_068937
  · exact g32p_supplierForest_actual_068941
  · exact g32p_supplierForest_actual_068962
  · exact g32p_supplierForest_actual_068968
  · exact g32p_supplierForest_actual_068972
  · exact g32p_supplierForest_actual_069044
  · exact g32p_supplierForest_actual_069076
  · exact g32p_supplierForest_actual_069094
  · exact g32p_supplierForest_actual_069101
  · exact g32p_supplierForest_actual_069139
  · exact g32p_supplierForest_actual_069147
  · exact g32p_supplierForest_actual_069160
  · exact g32p_supplierForest_actual_069168
  · exact g32p_supplierForest_actual_069257
  · exact g32p_supplierForest_actual_069364
  · exact g32p_supplierForest_actual_069373
  · exact g32p_supplierForest_actual_069392
  · exact g32p_supplierForest_actual_069461
  · exact g32p_supplierForest_actual_069487
  · exact g32p_supplierForest_actual_069574
  · exact g32p_supplierForest_actual_069688
  · exact g32p_supplierForest_actual_069710
  · exact g32p_supplierForest_actual_069717
  · exact g32p_supplierForest_actual_069722
  · exact g32p_supplierForest_actual_069744
  · exact g32p_supplierForest_actual_069770
  · exact g32p_supplierForest_actual_069858
  · exact g32p_supplierForest_actual_069905
  · exact g32p_supplierForest_actual_069939
  · exact g32p_supplierForest_actual_069982
  · exact g32p_supplierForest_actual_069985
  · exact g32p_supplierForest_actual_069989
  · exact g32p_supplierForest_actual_070012
  · exact g32p_supplierForest_actual_070056
  · exact g32p_supplierForest_actual_070096
  · exact g32p_supplierForest_actual_070115
  · exact g32p_supplierForest_actual_070134
  · exact g32p_supplierForest_actual_070150
  · exact g32p_supplierForest_actual_070199
  · exact g32p_supplierForest_actual_070236
  · exact g32p_supplierForest_actual_070248
  · exact g32p_supplierForest_actual_070324
  · exact g32p_supplierForest_actual_070338
  · exact g32p_supplierForest_actual_070392
  · exact g32p_supplierForest_actual_070404
  · exact g32p_supplierForest_actual_070428
  · exact g32p_supplierForest_actual_070430
  · exact g32p_supplierForest_actual_070467
  · exact g32p_supplierForest_actual_070578
  · exact g32p_supplierForest_actual_070597
  · exact g32p_supplierForest_actual_070602
  · exact g32p_supplierForest_actual_070749
  · exact g32p_supplierForest_actual_070763
  · exact g32p_supplierForest_actual_070780
  · exact g32p_supplierForest_actual_070785
  · exact g32p_supplierForest_actual_070879
  · exact g32p_supplierForest_actual_070909
  · exact g32p_supplierForest_actual_070961
  · exact g32p_supplierForest_actual_071157
  · exact g32p_supplierForest_actual_071167
  · exact g32p_supplierForest_actual_071172
  · exact g32p_supplierForest_actual_071181
  · exact g32p_supplierForest_actual_071191
  · exact g32p_supplierForest_actual_071194
  · exact g32p_supplierForest_actual_071203
  · exact g32p_supplierForest_actual_071257
  · exact g32p_supplierForest_actual_071306
  · exact g32p_supplierForest_actual_071309
  · exact g32p_supplierForest_actual_071339
  · exact g32p_supplierForest_actual_071398
  · exact g32p_supplierForest_actual_071399
  · exact g32p_supplierForest_actual_071413
  · exact g32p_supplierForest_actual_071427
  · exact g32p_supplierForest_actual_071462
  · exact g32p_supplierForest_actual_071463
  · exact g32p_supplierForest_actual_071467
  · exact g32p_supplierForest_actual_071494
  · exact g32p_supplierForest_actual_071495
  · exact g32p_supplierForest_actual_071504
  · exact g32p_supplierForest_actual_071570
  · exact g32p_supplierForest_actual_071612
  · exact g32p_supplierForest_actual_071623
  · exact g32p_supplierForest_actual_071753
  · exact g32p_supplierForest_actual_071762
  · exact g32p_supplierForest_actual_071785
  · exact g32p_supplierForest_actual_071791
  · exact g32p_supplierForest_actual_071811
  · exact g32p_supplierForest_actual_071822
  · exact g32p_supplierForest_actual_071835
  · exact g32p_supplierForest_actual_071913
  · exact g32p_supplierForest_actual_071914
  · exact g32p_supplierForest_actual_072012
  · exact g32p_supplierForest_actual_072037
  · exact g32p_supplierForest_actual_072041
  · exact g32p_supplierForest_actual_072113
  · exact g32p_supplierForest_actual_072145
  · exact g32p_supplierForest_actual_072206
  · exact g32p_supplierForest_actual_072209
  · exact g32p_supplierForest_actual_072335
  · exact g32p_supplierForest_actual_072375
  · exact g32p_supplierForest_actual_072403
  · exact g32p_supplierForest_actual_072411
  · exact g32p_supplierForest_actual_072517
  · exact g32p_supplierForest_actual_072523
  · exact g32p_supplierForest_actual_072612
  · exact g32p_supplierForest_actual_072616
  · exact g32p_supplierForest_actual_072617
  · exact g32p_supplierForest_actual_072632
  · exact g32p_supplierForest_actual_072662
  · exact g32p_supplierForest_actual_072687
  · exact g32p_supplierForest_actual_072719
  · exact g32p_supplierForest_actual_072724
  · exact g32p_supplierForest_actual_072738
  · exact g32p_supplierForest_actual_072802
  · exact g32p_supplierForest_actual_072805
  · exact g32p_supplierForest_actual_072814
  · exact g32p_supplierForest_actual_072820
  · exact g32p_supplierForest_actual_072823
  · exact g32p_supplierForest_actual_072885
  · exact g32p_supplierForest_actual_072902
  · exact g32p_supplierForest_actual_072921
  · exact g32p_supplierForest_actual_073002
  · exact g32p_supplierForest_actual_073140
  · exact g32p_supplierForest_actual_073155

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_073186 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073186 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073186 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_015333 := by
  decide +kernel

theorem g32p_supplierForest_actual_073186 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073186) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_073186
    g32p_supplierForest_actual_015333

def g32p_supplierForest_node_073239 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073239 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073239 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015282 := by
  decide +kernel

theorem g32p_supplierForest_actual_073239 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073239) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_073239
    g32p_supplierForest_actual_015282

def g32p_supplierForest_node_073286 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073286 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073286 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083280 := by
  decide +kernel

theorem g32p_supplierForest_actual_073286 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073286) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_073286
    g32p_supplierForest_actual_083280

def g32p_supplierForest_node_073289 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073289 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073289 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073381 := by
  decide +kernel

theorem g32p_supplierForest_actual_073289 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073289) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_073289
    g32p_supplierForest_actual_073381

def g32p_supplierForest_node_073325 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073325 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073325 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_084438 := by
  decide +kernel

theorem g32p_supplierForest_actual_073325 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073325) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_073325
    g32p_supplierForest_actual_084438

def g32p_supplierForest_node_073373 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073373 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073373 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_023595 := by
  decide +kernel

theorem g32p_supplierForest_actual_073373 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073373) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_073373
    g32p_supplierForest_actual_023595

def g32p_supplierForest_node_073383 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073383 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073383 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083274 := by
  decide +kernel

theorem g32p_supplierForest_actual_073383 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073383) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 3 g32p_supplierForest_edge_073383
    g32p_supplierForest_actual_083274

def g32p_supplierForest_node_073394 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073394 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073394 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074459 := by
  decide +kernel

theorem g32p_supplierForest_actual_073394 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073394) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_073394
    g32p_supplierForest_actual_074459

def g32p_supplierForest_node_073450 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_073450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073450 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021063 := by
  decide +kernel

theorem g32p_supplierForest_actual_073450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073450) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_073450
    g32p_supplierForest_actual_021063

def g32p_supplierForest_node_073452 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073452 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073452 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014808 := by
  decide +kernel

theorem g32p_supplierForest_actual_073452 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073452) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_073452
    g32p_supplierForest_actual_014808

def g32p_supplierForest_node_073460 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_073460 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073460 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083673 := by
  decide +kernel

theorem g32p_supplierForest_actual_073460 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073460) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_073460
    g32p_supplierForest_actual_083673

def g32p_supplierForest_node_073461 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073461 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073461 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015232 := by
  decide +kernel

theorem g32p_supplierForest_actual_073461 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073461) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_073461
    g32p_supplierForest_actual_015232

def g32p_supplierForest_node_073495 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073495 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073495 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_015434 := by
  decide +kernel

theorem g32p_supplierForest_actual_073495 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073495) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_073495
    g32p_supplierForest_actual_015434

def g32p_supplierForest_node_073497 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073497 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073497 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074919 := by
  decide +kernel

theorem g32p_supplierForest_actual_073497 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073497) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_073497
    g32p_supplierForest_actual_074919

def g32p_supplierForest_node_073504 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073504 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074264 := by
  decide +kernel

theorem g32p_supplierForest_actual_073504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073504) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_073504
    g32p_supplierForest_actual_074264

def g32p_supplierForest_node_073585 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073585 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021662 := by
  decide +kernel

theorem g32p_supplierForest_actual_073585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073585) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_073585
    g32p_supplierForest_actual_021662

def g32p_supplierForest_node_073606 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_073606 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073606 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085294 := by
  decide +kernel

theorem g32p_supplierForest_actual_073606 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073606) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_073606
    g32p_supplierForest_actual_085294

def g32p_supplierForest_node_073633 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_073633 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073633 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_019932 := by
  decide +kernel

theorem g32p_supplierForest_actual_073633 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073633) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 0 g32p_supplierForest_edge_073633
    g32p_supplierForest_actual_019932

def g32p_supplierForest_node_073649 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073649 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073649 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073906 := by
  decide +kernel

theorem g32p_supplierForest_actual_073649 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073649) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_073649
    g32p_supplierForest_actual_073906

def g32p_supplierForest_node_073654 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073654 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073654 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083894 := by
  decide +kernel

theorem g32p_supplierForest_actual_073654 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073654) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_073654
    g32p_supplierForest_actual_083894

def g32p_supplierForest_node_073679 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_073679 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073679 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021063 := by
  decide +kernel

theorem g32p_supplierForest_actual_073679 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073679) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_073679
    g32p_supplierForest_actual_021063

def g32p_supplierForest_node_073685 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_073685 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073685 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019134 := by
  decide +kernel

theorem g32p_supplierForest_actual_073685 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073685) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_073685
    g32p_supplierForest_actual_019134

def g32p_supplierForest_node_073711 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073711 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073711 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014899 := by
  decide +kernel

theorem g32p_supplierForest_actual_073711 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073711) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_073711
    g32p_supplierForest_actual_014899

def g32p_supplierForest_node_073727 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073727 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073727 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012374 := by
  decide +kernel

theorem g32p_supplierForest_actual_073727 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073727) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_073727
    g32p_supplierForest_actual_012374

def g32p_supplierForest_node_073758 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073758 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073758 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073755 := by
  decide +kernel

theorem g32p_supplierForest_actual_073758 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073758) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_073758
    g32p_supplierForest_actual_073755

def g32p_supplierForest_node_073776 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_073776 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073776 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018438 := by
  decide +kernel

theorem g32p_supplierForest_actual_073776 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073776) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_073776
    g32p_supplierForest_actual_018438

def g32p_supplierForest_node_073805 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073805 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073805 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074285 := by
  decide +kernel

theorem g32p_supplierForest_actual_073805 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073805) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_073805
    g32p_supplierForest_actual_074285

def g32p_supplierForest_node_073891 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073891 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073891 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074472 := by
  decide +kernel

theorem g32p_supplierForest_actual_073891 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073891) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_073891
    g32p_supplierForest_actual_074472

def g32p_supplierForest_node_073921 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073921 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073921 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_078853 := by
  decide +kernel

theorem g32p_supplierForest_actual_073921 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073921) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_073921
    g32p_supplierForest_actual_078853

def g32p_supplierForest_node_073963 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_073963 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073963 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_024270 := by
  decide +kernel

theorem g32p_supplierForest_actual_073963 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073963) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_073963
    g32p_supplierForest_actual_024270

def g32p_supplierForest_node_074000 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_074000 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074000 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_024295 := by
  decide +kernel

theorem g32p_supplierForest_actual_074000 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074000) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_074000
    g32p_supplierForest_actual_024295

def g32p_supplierForest_node_074005 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074005 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074005 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092777 := by
  decide +kernel

theorem g32p_supplierForest_actual_074005 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074005) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_074005
    g32p_supplierForest_actual_092777

def g32p_supplierForest_node_074009 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074009 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074009 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_078105 := by
  decide +kernel

theorem g32p_supplierForest_actual_074009 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074009) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_074009
    g32p_supplierForest_actual_078105

def g32p_supplierForest_node_074030 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_074030 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074030 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018200 := by
  decide +kernel

theorem g32p_supplierForest_actual_074030 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074030) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_074030
    g32p_supplierForest_actual_018200

def g32p_supplierForest_node_074074 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_074074 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074074 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_079690 := by
  decide +kernel

theorem g32p_supplierForest_actual_074074 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074074) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_074074
    g32p_supplierForest_actual_079690

def g32p_supplierForest_node_074131 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_074131 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074131 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021947 := by
  decide +kernel

theorem g32p_supplierForest_actual_074131 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074131) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_074131
    g32p_supplierForest_actual_021947

def g32p_supplierForest_node_074184 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074184 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074184 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074188 := by
  decide +kernel

theorem g32p_supplierForest_actual_074184 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074184) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_074184
    g32p_supplierForest_actual_074188

def g32p_supplierForest_node_074200 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_074200 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074200 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_021079 := by
  decide +kernel

theorem g32p_supplierForest_actual_074200 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074200) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_074200
    g32p_supplierForest_actual_021079

def g32p_supplierForest_node_074205 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074205 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083673 := by
  decide +kernel

theorem g32p_supplierForest_actual_074205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074205) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_074205
    g32p_supplierForest_actual_083673

def g32p_supplierForest_node_074284 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074284 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074284 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015232 := by
  decide +kernel

theorem g32p_supplierForest_actual_074284 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074284) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_074284
    g32p_supplierForest_actual_015232

def g32p_supplierForest_node_074291 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_074291 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074291 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014868 := by
  decide +kernel

theorem g32p_supplierForest_actual_074291 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074291) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 2 g32p_supplierForest_edge_074291
    g32p_supplierForest_actual_014868

def g32p_supplierForest_node_074342 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_074342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074342 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012764 := by
  decide +kernel

theorem g32p_supplierForest_actual_074342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074342) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_074342
    g32p_supplierForest_actual_012764

def g32p_supplierForest_node_074374 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074374 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074374 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_017981 := by
  decide +kernel

theorem g32p_supplierForest_actual_074374 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074374) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_074374
    g32p_supplierForest_actual_017981

def g32p_supplierForest_node_074445 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_074445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074445 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013086 := by
  decide +kernel

theorem g32p_supplierForest_actual_074445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074445) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_074445
    g32p_supplierForest_actual_013086

def g32p_supplierForest_node_074456 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_074456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074456 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015175 := by
  decide +kernel

theorem g32p_supplierForest_actual_074456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074456) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_074456
    g32p_supplierForest_actual_015175

def g32p_supplierForest_node_074465 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_074465 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074465 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_086435 := by
  decide +kernel

theorem g32p_supplierForest_actual_074465 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074465) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_074465
    g32p_supplierForest_actual_086435

def g32p_supplierForest_node_074475 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074475 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074475 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013385 := by
  decide +kernel

theorem g32p_supplierForest_actual_074475 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074475) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_074475
    g32p_supplierForest_actual_013385

def g32p_supplierForest_node_074504 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_074504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074504 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012579 := by
  decide +kernel

theorem g32p_supplierForest_actual_074504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074504) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_074504
    g32p_supplierForest_actual_012579

def g32p_supplierForest_node_074602 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074602 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074602 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015333 := by
  decide +kernel

theorem g32p_supplierForest_actual_074602 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074602) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_074602
    g32p_supplierForest_actual_015333

def g32p_supplierForest_node_074614 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_074614 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074614 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092764 := by
  decide +kernel

theorem g32p_supplierForest_actual_074614 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074614) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_074614
    g32p_supplierForest_actual_092764

def g32p_supplierForest_node_074695 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074695 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074695 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075457 := by
  decide +kernel

theorem g32p_supplierForest_actual_074695 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074695) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_074695
    g32p_supplierForest_actual_075457

def g32p_supplierForest_node_074787 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074787 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074787 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085696 := by
  decide +kernel

theorem g32p_supplierForest_actual_074787 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074787) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_074787
    g32p_supplierForest_actual_085696

def g32p_supplierForest_node_074789 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074789 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012995 := by
  decide +kernel

theorem g32p_supplierForest_actual_074789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074789) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 2 g32p_supplierForest_edge_074789
    g32p_supplierForest_actual_012995

def g32p_supplierForest_node_074854 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074854 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074854 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146434 := by
  decide +kernel

theorem g32p_supplierForest_actual_074854 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074854) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_074854
    g32p_supplierForest_actual_146434

def g32p_supplierForest_node_074901 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074901 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074901 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019230 := by
  decide +kernel

theorem g32p_supplierForest_actual_074901 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074901) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_074901
    g32p_supplierForest_actual_019230

def g32p_supplierForest_node_074916 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_074916 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074916 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083512 := by
  decide +kernel

theorem g32p_supplierForest_actual_074916 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074916) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_074916
    g32p_supplierForest_actual_083512

def g32p_supplierForest_node_075036 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_075036 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075036 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085542 := by
  decide +kernel

theorem g32p_supplierForest_actual_075036 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075036) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_075036
    g32p_supplierForest_actual_085542

def g32p_supplierForest_node_075159 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_075159 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075159 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_147333 := by
  decide +kernel

theorem g32p_supplierForest_actual_075159 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075159) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_075159
    g32p_supplierForest_actual_147333

def g32p_supplierForest_node_075176 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_075176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075176 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076546 := by
  decide +kernel

theorem g32p_supplierForest_actual_075176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075176) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_075176
    g32p_supplierForest_actual_076546

def g32p_supplierForest_node_075182 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_075182 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075182 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012326 := by
  decide +kernel

theorem g32p_supplierForest_actual_075182 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075182) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_075182
    g32p_supplierForest_actual_012326

def g32p_supplierForest_node_075214 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075214 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075214 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075370 := by
  decide +kernel

theorem g32p_supplierForest_actual_075214 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075214) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_075214
    g32p_supplierForest_actual_075370

def g32p_supplierForest_node_075217 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075217 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_018262 := by
  decide +kernel

theorem g32p_supplierForest_actual_075217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075217) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_075217
    g32p_supplierForest_actual_018262

def g32p_supplierForest_node_075264 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_075264 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075264 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101034 := by
  decide +kernel

theorem g32p_supplierForest_actual_075264 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075264) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_075264
    g32p_supplierForest_actual_101034

def g32p_supplierForest_node_075284 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_075284 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075284 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012374 := by
  decide +kernel

theorem g32p_supplierForest_actual_075284 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075284) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 2 g32p_supplierForest_edge_075284
    g32p_supplierForest_actual_012374

def g32p_supplierForest_node_075386 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075386 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075386 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092683 := by
  decide +kernel

theorem g32p_supplierForest_actual_075386 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075386) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_075386
    g32p_supplierForest_actual_092683

def g32p_supplierForest_node_075405 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_075405 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075405 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074264 := by
  decide +kernel

theorem g32p_supplierForest_actual_075405 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075405) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_075405
    g32p_supplierForest_actual_074264

def g32p_supplierForest_node_075447 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075447 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075447 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074285 := by
  decide +kernel

theorem g32p_supplierForest_actual_075447 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075447) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_075447
    g32p_supplierForest_actual_074285

def g32p_supplierForest_node_075459 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075459 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075459 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012755 := by
  decide +kernel

theorem g32p_supplierForest_actual_075459 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075459) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_075459
    g32p_supplierForest_actual_012755

def g32p_supplierForest_node_075463 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075463 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075463 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_085294 := by
  decide +kernel

theorem g32p_supplierForest_actual_075463 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075463) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_075463
    g32p_supplierForest_actual_085294

def g32p_supplierForest_node_075465 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075465 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075465 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075458 := by
  decide +kernel

theorem g32p_supplierForest_actual_075465 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075465) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 3 g32p_supplierForest_edge_075465
    g32p_supplierForest_actual_075458

def g32p_supplierForest_node_075469 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075469 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075469 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082862 := by
  decide +kernel

theorem g32p_supplierForest_actual_075469 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075469) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 0 g32p_supplierForest_edge_075469
    g32p_supplierForest_actual_082862

def g32p_supplierForest_node_075531 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075531 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_017997 := by
  decide +kernel

theorem g32p_supplierForest_actual_075531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075531) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_075531
    g32p_supplierForest_actual_017997

def g32p_supplierForest_node_075534 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_075534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075534 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_016215 := by
  decide +kernel

theorem g32p_supplierForest_actual_075534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075534) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_075534
    g32p_supplierForest_actual_016215

def g32p_supplierForest_node_075582 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075582 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075582 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083881 := by
  decide +kernel

theorem g32p_supplierForest_actual_075582 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075582) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_075582
    g32p_supplierForest_actual_083881

def g32p_supplierForest_node_075655 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_075655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075655 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015911 := by
  decide +kernel

theorem g32p_supplierForest_actual_075655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075655) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_075655
    g32p_supplierForest_actual_015911

def g32p_supplierForest_node_075667 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_075667 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075667 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092598 := by
  decide +kernel

theorem g32p_supplierForest_actual_075667 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075667) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_075667
    g32p_supplierForest_actual_092598

def g32p_supplierForest_node_075774 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075774 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075774 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012383 := by
  decide +kernel

theorem g32p_supplierForest_actual_075774 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075774) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 3 g32p_supplierForest_edge_075774
    g32p_supplierForest_actual_012383

def g32p_supplierForest_node_075779 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075779 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075779 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076745 := by
  decide +kernel

theorem g32p_supplierForest_actual_075779 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075779) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_075779
    g32p_supplierForest_actual_076745

def g32p_supplierForest_node_075785 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075785 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013362 := by
  decide +kernel

theorem g32p_supplierForest_actual_075785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075785) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_075785
    g32p_supplierForest_actual_013362

def g32p_supplierForest_node_075786 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075786 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075786 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013086 := by
  decide +kernel

theorem g32p_supplierForest_actual_075786 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075786) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_075786
    g32p_supplierForest_actual_013086

def g32p_supplierForest_node_075792 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075792 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075792 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_023694 := by
  decide +kernel

theorem g32p_supplierForest_actual_075792 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075792) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_075792
    g32p_supplierForest_actual_023694

def g32p_supplierForest_node_075801 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075801 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014971 := by
  decide +kernel

theorem g32p_supplierForest_actual_075801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075801) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_075801
    g32p_supplierForest_actual_014971

def g32p_supplierForest_node_075821 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075821 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075821 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097265 := by
  decide +kernel

theorem g32p_supplierForest_actual_075821 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075821) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_075821
    g32p_supplierForest_actual_097265

def g32p_supplierForest_node_075855 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075855 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075855 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077885 := by
  decide +kernel

theorem g32p_supplierForest_actual_075855 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075855) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_075855
    g32p_supplierForest_actual_077885

def g32p_supplierForest_node_075906 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075906 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075906 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092808 := by
  decide +kernel

theorem g32p_supplierForest_actual_075906 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075906) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_075906
    g32p_supplierForest_actual_092808

def g32p_supplierForest_node_075968 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075968 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075968 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_086621 := by
  decide +kernel

theorem g32p_supplierForest_actual_075968 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075968) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_075968
    g32p_supplierForest_actual_086621

def g32p_supplierForest_node_076174 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076174 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020387 := by
  decide +kernel

theorem g32p_supplierForest_actual_076174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076174) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_076174
    g32p_supplierForest_actual_020387

def g32p_supplierForest_node_076208 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076208 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076208 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018553 := by
  decide +kernel

theorem g32p_supplierForest_actual_076208 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076208) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_076208
    g32p_supplierForest_actual_018553

def g32p_supplierForest_node_076223 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_076223 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076223 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013116 := by
  decide +kernel

theorem g32p_supplierForest_actual_076223 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076223) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_076223
    g32p_supplierForest_actual_013116

def g32p_supplierForest_node_076258 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076258 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076258 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074908 := by
  decide +kernel

theorem g32p_supplierForest_actual_076258 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076258) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_076258
    g32p_supplierForest_actual_074908

def g32p_supplierForest_node_076319 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076319 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_097542 := by
  decide +kernel

theorem g32p_supplierForest_actual_076319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076319) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 3 g32p_supplierForest_edge_076319
    g32p_supplierForest_actual_097542

def g32p_supplierForest_node_076326 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_076326 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076326 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074190 := by
  decide +kernel

theorem g32p_supplierForest_actual_076326 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076326) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_076326
    g32p_supplierForest_actual_074190

def g32p_supplierForest_node_076373 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076373 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076373 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_024270 := by
  decide +kernel

theorem g32p_supplierForest_actual_076373 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076373) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_076373
    g32p_supplierForest_actual_024270

def g32p_supplierForest_node_076390 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_076390 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076390 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073043 := by
  decide +kernel

theorem g32p_supplierForest_actual_076390 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076390) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_076390
    g32p_supplierForest_actual_073043

def g32p_supplierForest_node_076401 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_076401 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076401 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083944 := by
  decide +kernel

theorem g32p_supplierForest_actual_076401 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076401) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_076401
    g32p_supplierForest_actual_083944

def g32p_supplierForest_node_076406 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076406 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076406 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015911 := by
  decide +kernel

theorem g32p_supplierForest_actual_076406 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076406) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_076406
    g32p_supplierForest_actual_015911

def g32p_supplierForest_node_076451 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076451 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076451 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019719 := by
  decide +kernel

theorem g32p_supplierForest_actual_076451 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076451) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_076451
    g32p_supplierForest_actual_019719

def g32p_supplierForest_node_076477 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076477 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076477 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073114 := by
  decide +kernel

theorem g32p_supplierForest_actual_076477 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076477) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_076477
    g32p_supplierForest_actual_073114

def g32p_supplierForest_node_076516 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076516 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076516 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_071765 := by
  decide +kernel

theorem g32p_supplierForest_actual_076516 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076516) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_076516
    g32p_supplierForest_actual_071765

def g32p_supplierForest_node_076662 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076662 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076662 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021443 := by
  decide +kernel

theorem g32p_supplierForest_actual_076662 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076662) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 0 g32p_supplierForest_edge_076662
    g32p_supplierForest_actual_021443

def g32p_supplierForest_node_076665 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076665 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076665 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_016001 := by
  decide +kernel

theorem g32p_supplierForest_actual_076665 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076665) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 0 g32p_supplierForest_edge_076665
    g32p_supplierForest_actual_016001

def g32p_supplierForest_node_076767 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_076767 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076767 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016215 := by
  decide +kernel

theorem g32p_supplierForest_actual_076767 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076767) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_076767
    g32p_supplierForest_actual_016215

def g32p_supplierForest_node_076780 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076780 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076780 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016851 := by
  decide +kernel

theorem g32p_supplierForest_actual_076780 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076780) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_076780
    g32p_supplierForest_actual_016851

def g32p_supplierForest_node_076898 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_076898 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076898 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087745 := by
  decide +kernel

theorem g32p_supplierForest_actual_076898 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076898) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_076898
    g32p_supplierForest_actual_087745

def g32p_supplierForest_node_076943 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_076943 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076943 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082969 := by
  decide +kernel

theorem g32p_supplierForest_actual_076943 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076943) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_076943
    g32p_supplierForest_actual_082969

def g32p_supplierForest_node_076948 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_076948 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076948 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082035 := by
  decide +kernel

theorem g32p_supplierForest_actual_076948 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076948) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 0 g32p_supplierForest_edge_076948
    g32p_supplierForest_actual_082035

def g32p_supplierForest_node_077044 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_077044 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077044 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018262 := by
  decide +kernel

theorem g32p_supplierForest_actual_077044 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077044) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_077044
    g32p_supplierForest_actual_018262

def g32p_supplierForest_node_077081 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_077081 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077081 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093309 := by
  decide +kernel

theorem g32p_supplierForest_actual_077081 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077081) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_077081
    g32p_supplierForest_actual_093309

def g32p_supplierForest_node_077110 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_077110 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077110 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075947 := by
  decide +kernel

theorem g32p_supplierForest_actual_077110 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077110) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 2 g32p_supplierForest_edge_077110
    g32p_supplierForest_actual_075947

def g32p_supplierForest_node_077188 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_077188 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077188 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_016201 := by
  decide +kernel

theorem g32p_supplierForest_actual_077188 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077188) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_077188
    g32p_supplierForest_actual_016201

def g32p_supplierForest_node_077194 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077194 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077194 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088102 := by
  decide +kernel

theorem g32p_supplierForest_actual_077194 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077194) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_077194
    g32p_supplierForest_actual_088102

def g32p_supplierForest_node_077197 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077197 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077197 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023537 := by
  decide +kernel

theorem g32p_supplierForest_actual_077197 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077197) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_077197
    g32p_supplierForest_actual_023537

def g32p_supplierForest_node_077211 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077211 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077211 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_086327 := by
  decide +kernel

theorem g32p_supplierForest_actual_077211 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077211) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_077211
    g32p_supplierForest_actual_086327

def g32p_supplierForest_node_077250 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077250 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077250 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098235 := by
  decide +kernel

theorem g32p_supplierForest_actual_077250 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077250) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_077250
    g32p_supplierForest_actual_098235

def g32p_supplierForest_node_077271 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_077271 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077271 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088185 := by
  decide +kernel

theorem g32p_supplierForest_actual_077271 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077271) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_077271
    g32p_supplierForest_actual_088185

def g32p_supplierForest_node_077290 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_077290 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077290 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076945 := by
  decide +kernel

theorem g32p_supplierForest_actual_077290 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077290) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_077290
    g32p_supplierForest_actual_076945

def g32p_supplierForest_node_077296 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_077296 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077296 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076972 := by
  decide +kernel

theorem g32p_supplierForest_actual_077296 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077296) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_077296
    g32p_supplierForest_actual_076972

def g32p_supplierForest_node_077321 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_077321 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077321 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_015542 := by
  decide +kernel

theorem g32p_supplierForest_actual_077321 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077321) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_077321
    g32p_supplierForest_actual_015542

def g32p_supplierForest_node_077370 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077370 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077370 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018190 := by
  decide +kernel

theorem g32p_supplierForest_actual_077370 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077370) ∧
        IsConj g (g32p_literalRepresentative 51) := by
  exact g32p_archive_step_lift _ _ 51 1 g32p_supplierForest_edge_077370
    g32p_supplierForest_actual_018190

def g32p_supplierForest_node_077394 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077394 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077394 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071941 := by
  decide +kernel

theorem g32p_supplierForest_actual_077394 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077394) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_077394
    g32p_supplierForest_actual_071941

def g32p_supplierForest_node_077405 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077405 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077405 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077391 := by
  decide +kernel

theorem g32p_supplierForest_actual_077405 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077405) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_077405
    g32p_supplierForest_actual_077391

def g32p_supplierForest_node_077456 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077456 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_017694 := by
  decide +kernel

theorem g32p_supplierForest_actual_077456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077456) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_077456
    g32p_supplierForest_actual_017694

def g32p_supplierForest_node_077463 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077463 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077463 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_144822 := by
  decide +kernel

theorem g32p_supplierForest_actual_077463 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077463) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_077463
    g32p_supplierForest_actual_144822

def g32p_supplierForest_node_077474 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_077474 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077474 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077354 := by
  decide +kernel

theorem g32p_supplierForest_actual_077474 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077474) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_077474
    g32p_supplierForest_actual_077354

def g32p_supplierForest_node_077491 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077491 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077491 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013362 := by
  decide +kernel

theorem g32p_supplierForest_actual_077491 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077491) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_077491
    g32p_supplierForest_actual_013362

def g32p_supplierForest_node_077537 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077537 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077537 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088499 := by
  decide +kernel

theorem g32p_supplierForest_actual_077537 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077537) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_077537
    g32p_supplierForest_actual_088499

def g32p_supplierForest_node_077547 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_077547 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077547 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073114 := by
  decide +kernel

theorem g32p_supplierForest_actual_077547 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077547) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_077547
    g32p_supplierForest_actual_073114

def g32p_supplierForest_node_077564 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_077564 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077564 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073346 := by
  decide +kernel

theorem g32p_supplierForest_actual_077564 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077564) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_077564
    g32p_supplierForest_actual_073346

def g32p_supplierForest_node_077576 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077576 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077576 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073381 := by
  decide +kernel

theorem g32p_supplierForest_actual_077576 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077576) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_077576
    g32p_supplierForest_actual_073381

def g32p_supplierForest_node_077783 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077783 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074472 := by
  decide +kernel

theorem g32p_supplierForest_actual_077783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077783) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_077783
    g32p_supplierForest_actual_074472

def g32p_supplierForest_node_077822 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077822 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077822 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084173 := by
  decide +kernel

theorem g32p_supplierForest_actual_077822 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077822) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_077822
    g32p_supplierForest_actual_084173

def g32p_supplierForest_node_077841 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_077841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077841 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074190 := by
  decide +kernel

theorem g32p_supplierForest_actual_077841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077841) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_077841
    g32p_supplierForest_actual_074190

def g32p_supplierForest_node_077845 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_077845 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077845 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014868 := by
  decide +kernel

theorem g32p_supplierForest_actual_077845 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077845) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 3 g32p_supplierForest_edge_077845
    g32p_supplierForest_actual_014868

def g32p_supplierForest_node_077921 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077921 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077921 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075492 := by
  decide +kernel

theorem g32p_supplierForest_actual_077921 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077921) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_077921
    g32p_supplierForest_actual_075492

def g32p_supplierForest_node_077923 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077923 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077923 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074742 := by
  decide +kernel

theorem g32p_supplierForest_actual_077923 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077923) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_077923
    g32p_supplierForest_actual_074742

def g32p_supplierForest_node_078020 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_078020 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078020 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074968 := by
  decide +kernel

theorem g32p_supplierForest_actual_078020 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078020) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_078020
    g32p_supplierForest_actual_074968

def g32p_supplierForest_node_078051 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_078051 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078051 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_089058 := by
  decide +kernel

theorem g32p_supplierForest_actual_078051 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078051) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 0 g32p_supplierForest_edge_078051
    g32p_supplierForest_actual_089058

def g32p_supplierForest_node_078052 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_078052 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078052 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083593 := by
  decide +kernel

theorem g32p_supplierForest_actual_078052 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078052) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_078052
    g32p_supplierForest_actual_083593

def g32p_supplierForest_node_078079 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_078079 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078079 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078047 := by
  decide +kernel

theorem g32p_supplierForest_actual_078079 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078079) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_078079
    g32p_supplierForest_actual_078047

def g32p_supplierForest_node_078097 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078097 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078097 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078096 := by
  decide +kernel

theorem g32p_supplierForest_actual_078097 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078097) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 1 g32p_supplierForest_edge_078097
    g32p_supplierForest_actual_078096

def g32p_supplierForest_node_078109 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078109 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078109 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076527 := by
  decide +kernel

theorem g32p_supplierForest_actual_078109 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078109) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_078109
    g32p_supplierForest_actual_076527

def g32p_supplierForest_node_078155 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_078155 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078155 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_088645 := by
  decide +kernel

theorem g32p_supplierForest_actual_078155 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078155) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 1 g32p_supplierForest_edge_078155
    g32p_supplierForest_actual_088645

def g32p_supplierForest_node_078255 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_078255 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078255 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084393 := by
  decide +kernel

theorem g32p_supplierForest_actual_078255 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078255) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_078255
    g32p_supplierForest_actual_084393

def g32p_supplierForest_node_078304 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_078304 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078304 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_089361 := by
  decide +kernel

theorem g32p_supplierForest_actual_078304 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078304) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_078304
    g32p_supplierForest_actual_089361

def g32p_supplierForest_node_078385 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078385 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078385 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071765 := by
  decide +kernel

theorem g32p_supplierForest_actual_078385 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078385) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_078385
    g32p_supplierForest_actual_071765

def g32p_supplierForest_node_078399 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_078399 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078399 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071746 := by
  decide +kernel

theorem g32p_supplierForest_actual_078399 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078399) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_078399
    g32p_supplierForest_actual_071746

def g32p_supplierForest_node_078404 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078404 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078404 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013309 := by
  decide +kernel

theorem g32p_supplierForest_actual_078404 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078404) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_078404
    g32p_supplierForest_actual_013309

def g32p_supplierForest_node_078409 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_078409 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078409 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077231 := by
  decide +kernel

theorem g32p_supplierForest_actual_078409 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078409) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_078409
    g32p_supplierForest_actual_077231

def g32p_supplierForest_node_078426 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078426 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078426 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013320 := by
  decide +kernel

theorem g32p_supplierForest_actual_078426 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078426) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_078426
    g32p_supplierForest_actual_013320

def g32p_supplierForest_node_078499 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078499 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078499 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013349 := by
  decide +kernel

theorem g32p_supplierForest_actual_078499 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078499) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_078499
    g32p_supplierForest_actual_013349

def g32p_supplierForest_node_078540 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_078540 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078540 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_017123 := by
  decide +kernel

theorem g32p_supplierForest_actual_078540 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078540) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_078540
    g32p_supplierForest_actual_017123

def g32p_supplierForest_node_078543 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_078543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078543 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076972 := by
  decide +kernel

theorem g32p_supplierForest_actual_078543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078543) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_078543
    g32p_supplierForest_actual_076972

def g32p_supplierForest_node_078545 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_078545 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078545 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014989 := by
  decide +kernel

theorem g32p_supplierForest_actual_078545 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078545) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_078545
    g32p_supplierForest_actual_014989

def g32p_supplierForest_node_078569 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_078569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078569 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076882 := by
  decide +kernel

theorem g32p_supplierForest_actual_078569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078569) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_078569
    g32p_supplierForest_actual_076882

def g32p_supplierForest_node_078700 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078700 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078700 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013496 := by
  decide +kernel

theorem g32p_supplierForest_actual_078700 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078700) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_078700
    g32p_supplierForest_actual_013496

def g32p_supplierForest_node_078808 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_078808 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078808 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152313 := by
  decide +kernel

theorem g32p_supplierForest_actual_078808 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078808) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_078808
    g32p_supplierForest_actual_152313

def g32p_supplierForest_node_078842 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_078842 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078842 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013614 := by
  decide +kernel

theorem g32p_supplierForest_actual_078842 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078842) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 3 g32p_supplierForest_edge_078842
    g32p_supplierForest_actual_013614

def g32p_supplierForest_node_078912 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078912 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078912 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_017291 := by
  decide +kernel

theorem g32p_supplierForest_actual_078912 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078912) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 2 g32p_supplierForest_edge_078912
    g32p_supplierForest_actual_017291

def g32p_supplierForest_node_078974 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_078974 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078974 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_017110 := by
  decide +kernel

theorem g32p_supplierForest_actual_078974 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078974) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_078974
    g32p_supplierForest_actual_017110

def g32p_supplierForest_node_079006 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_079006 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079006 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018296 := by
  decide +kernel

theorem g32p_supplierForest_actual_079006 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079006) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_079006
    g32p_supplierForest_actual_018296

def g32p_supplierForest_node_079019 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_079019 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079019 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089473 := by
  decide +kernel

theorem g32p_supplierForest_actual_079019 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079019) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_079019
    g32p_supplierForest_actual_089473

def g32p_supplierForest_node_079028 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_079028 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079028 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021790 := by
  decide +kernel

theorem g32p_supplierForest_actual_079028 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079028) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_079028
    g32p_supplierForest_actual_021790

def g32p_supplierForest_node_079056 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_079056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079056 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013823 := by
  decide +kernel

theorem g32p_supplierForest_actual_079056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079056) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_079056
    g32p_supplierForest_actual_013823

def g32p_supplierForest_node_079165 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_079165 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079165 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074506 := by
  decide +kernel

theorem g32p_supplierForest_actual_079165 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079165) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_079165
    g32p_supplierForest_actual_074506

def g32p_supplierForest_node_079189 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_079189 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079189 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076546 := by
  decide +kernel

theorem g32p_supplierForest_actual_079189 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079189) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_079189
    g32p_supplierForest_actual_076546

def g32p_supplierForest_node_079196 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_079196 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079196 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093830 := by
  decide +kernel

theorem g32p_supplierForest_actual_079196 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079196) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_079196
    g32p_supplierForest_actual_093830

def g32p_supplierForest_node_079198 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_079198 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079198 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089453 := by
  decide +kernel

theorem g32p_supplierForest_actual_079198 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079198) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_079198
    g32p_supplierForest_actual_089453

def g32p_supplierForest_node_079249 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_079249 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079249 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_080136 := by
  decide +kernel

theorem g32p_supplierForest_actual_079249 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079249) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 2 g32p_supplierForest_edge_079249
    g32p_supplierForest_actual_080136

def g32p_supplierForest_node_079284 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_079284 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079284 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_087489 := by
  decide +kernel

theorem g32p_supplierForest_actual_079284 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079284) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 1 g32p_supplierForest_edge_079284
    g32p_supplierForest_actual_087489

def g32p_supplierForest_node_079310 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_079310 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079310 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076834 := by
  decide +kernel

theorem g32p_supplierForest_actual_079310 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079310) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 2 g32p_supplierForest_edge_079310
    g32p_supplierForest_actual_076834

def g32p_supplierForest_node_079324 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_079324 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079324 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_090008 := by
  decide +kernel

theorem g32p_supplierForest_actual_079324 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079324) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_079324
    g32p_supplierForest_actual_090008

def g32p_supplierForest_node_079397 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_079397 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079397 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023450 := by
  decide +kernel

theorem g32p_supplierForest_actual_079397 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079397) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_079397
    g32p_supplierForest_actual_023450

def g32p_supplierForest_node_079445 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_079445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079445 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071746 := by
  decide +kernel

theorem g32p_supplierForest_actual_079445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079445) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_079445
    g32p_supplierForest_actual_071746

def g32p_supplierForest_node_079461 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_079461 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079461 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015500 := by
  decide +kernel

theorem g32p_supplierForest_actual_079461 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079461) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 2 g32p_supplierForest_edge_079461
    g32p_supplierForest_actual_015500

def g32p_supplierForest_node_079569 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_079569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079569 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074529 := by
  decide +kernel

theorem g32p_supplierForest_actual_079569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079569) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_079569
    g32p_supplierForest_actual_074529

def g32p_supplierForest_node_079590 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_079590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079590 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077391 := by
  decide +kernel

theorem g32p_supplierForest_actual_079590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079590) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_079590
    g32p_supplierForest_actual_077391

def g32p_supplierForest_node_079598 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_079598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079598 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_087069 := by
  decide +kernel

theorem g32p_supplierForest_actual_079598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079598) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_079598
    g32p_supplierForest_actual_087069

def g32p_supplierForest_node_079700 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_079700 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079700 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023195 := by
  decide +kernel

theorem g32p_supplierForest_actual_079700 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079700) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_079700
    g32p_supplierForest_actual_023195

def g32p_supplierForest_node_079796 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_079796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079796 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074747 := by
  decide +kernel

theorem g32p_supplierForest_actual_079796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079796) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 3 g32p_supplierForest_edge_079796
    g32p_supplierForest_actual_074747

def g32p_supplierForest_node_079890 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_079890 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079890 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014899 := by
  decide +kernel

theorem g32p_supplierForest_actual_079890 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079890) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 2 g32p_supplierForest_edge_079890
    g32p_supplierForest_actual_014899

def g32p_supplierForest_node_079900 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_079900 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079900 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012784 := by
  decide +kernel

theorem g32p_supplierForest_actual_079900 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079900) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_079900
    g32p_supplierForest_actual_012784

def g32p_supplierForest_node_079905 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_079905 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079905 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023417 := by
  decide +kernel

theorem g32p_supplierForest_actual_079905 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079905) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 0 g32p_supplierForest_edge_079905
    g32p_supplierForest_actual_023417

def g32p_supplierForest_node_079939 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_079939 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079939 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013496 := by
  decide +kernel

theorem g32p_supplierForest_actual_079939 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079939) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_079939
    g32p_supplierForest_actual_013496

def g32p_supplierForest_node_079970 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_079970 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079970 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083206 := by
  decide +kernel

theorem g32p_supplierForest_actual_079970 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079970) ∧
        IsConj g (g32p_literalRepresentative 81) := by
  exact g32p_archive_step_lift _ _ 81 2 g32p_supplierForest_edge_079970
    g32p_supplierForest_actual_083206

def g32p_supplierForest_node_079993 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_079993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079993 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080207 := by
  decide +kernel

theorem g32p_supplierForest_actual_079993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079993) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_079993
    g32p_supplierForest_actual_080207

def g32p_supplierForest_node_080011 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_080011 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080011 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074908 := by
  decide +kernel

theorem g32p_supplierForest_actual_080011 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080011) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_080011
    g32p_supplierForest_actual_074908

def g32p_supplierForest_node_080012 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080012 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080012 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085385 := by
  decide +kernel

theorem g32p_supplierForest_actual_080012 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080012) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_080012
    g32p_supplierForest_actual_085385

def g32p_supplierForest_node_080025 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_080025 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080025 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076729 := by
  decide +kernel

theorem g32p_supplierForest_actual_080025 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080025) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_080025
    g32p_supplierForest_actual_076729

def g32p_supplierForest_node_080067 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080067 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080067 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073746 := by
  decide +kernel

theorem g32p_supplierForest_actual_080067 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080067) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_080067
    g32p_supplierForest_actual_073746

def g32p_supplierForest_node_080090 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_080090 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080090 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074529 := by
  decide +kernel

theorem g32p_supplierForest_actual_080090 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080090) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_080090
    g32p_supplierForest_actual_074529

def g32p_supplierForest_node_080105 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_080105 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080105 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_074506 := by
  decide +kernel

theorem g32p_supplierForest_actual_080105 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080105) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_080105
    g32p_supplierForest_actual_074506

def g32p_supplierForest_node_080108 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_080108 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080108 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_090176 := by
  decide +kernel

theorem g32p_supplierForest_actual_080108 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080108) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_080108
    g32p_supplierForest_actual_090176

def g32p_supplierForest_node_080129 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_080129 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080129 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078302 := by
  decide +kernel

theorem g32p_supplierForest_actual_080129 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080129) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_080129
    g32p_supplierForest_actual_078302

def g32p_supplierForest_node_080179 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_080179 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080179 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086506 := by
  decide +kernel

theorem g32p_supplierForest_actual_080179 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080179) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_080179
    g32p_supplierForest_actual_086506

def g32p_supplierForest_node_080229 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_080229 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080229 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_016001 := by
  decide +kernel

theorem g32p_supplierForest_actual_080229 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080229) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 1 g32p_supplierForest_edge_080229
    g32p_supplierForest_actual_016001

def g32p_supplierForest_node_080291 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_080291 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080291 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073629 := by
  decide +kernel

theorem g32p_supplierForest_actual_080291 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080291) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_080291
    g32p_supplierForest_actual_073629

def g32p_supplierForest_node_080395 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080395 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080395 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077210 := by
  decide +kernel

theorem g32p_supplierForest_actual_080395 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080395) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 3 g32p_supplierForest_edge_080395
    g32p_supplierForest_actual_077210

def g32p_supplierForest_node_080462 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_080462 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080462 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073381 := by
  decide +kernel

theorem g32p_supplierForest_actual_080462 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080462) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_080462
    g32p_supplierForest_actual_073381

def g32p_supplierForest_node_080473 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_080473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080473 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093485 := by
  decide +kernel

theorem g32p_supplierForest_actual_080473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080473) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 1 g32p_supplierForest_edge_080473
    g32p_supplierForest_actual_093485

def g32p_supplierForest_node_080525 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080525 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080525 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_085473 := by
  decide +kernel

theorem g32p_supplierForest_actual_080525 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080525) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 1 g32p_supplierForest_edge_080525
    g32p_supplierForest_actual_085473

def g32p_supplierForest_node_080543 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_080543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080543 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091655 := by
  decide +kernel

theorem g32p_supplierForest_actual_080543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080543) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_080543
    g32p_supplierForest_actual_091655

def g32p_supplierForest_node_080590 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_080590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080590 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084438 := by
  decide +kernel

theorem g32p_supplierForest_actual_080590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080590) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_080590
    g32p_supplierForest_actual_084438

def g32p_supplierForest_node_080797 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_080797 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080797 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_018104 := by
  decide +kernel

theorem g32p_supplierForest_actual_080797 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080797) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_080797
    g32p_supplierForest_actual_018104

def g32p_supplierForest_node_080842 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_080842 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080842 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076882 := by
  decide +kernel

theorem g32p_supplierForest_actual_080842 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080842) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_080842
    g32p_supplierForest_actual_076882

def g32p_supplierForest_node_080983 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080983 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080983 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_013953 := by
  decide +kernel

theorem g32p_supplierForest_actual_080983 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080983) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 1 g32p_supplierForest_edge_080983
    g32p_supplierForest_actual_013953

def g32p_supplierForest_node_081005 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081005 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081005 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076729 := by
  decide +kernel

theorem g32p_supplierForest_actual_081005 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081005) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_081005
    g32p_supplierForest_actual_076729

def g32p_supplierForest_node_081044 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_081044 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081044 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079773 := by
  decide +kernel

theorem g32p_supplierForest_actual_081044 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081044) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 2 g32p_supplierForest_edge_081044
    g32p_supplierForest_actual_079773

def g32p_supplierForest_node_081069 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_081069 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081069 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_079094 := by
  decide +kernel

theorem g32p_supplierForest_actual_081069 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081069) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_081069
    g32p_supplierForest_actual_079094

def g32p_supplierForest_node_081071 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_081071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081071 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092219 := by
  decide +kernel

theorem g32p_supplierForest_actual_081071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081071) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_081071
    g32p_supplierForest_actual_092219

def g32p_supplierForest_node_081147 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081147 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081147 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015505 := by
  decide +kernel

theorem g32p_supplierForest_actual_081147 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081147) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_081147
    g32p_supplierForest_actual_015505

def g32p_supplierForest_node_081149 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_081149 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081149 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_147030 := by
  decide +kernel

theorem g32p_supplierForest_actual_081149 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081149) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_081149
    g32p_supplierForest_actual_147030

def g32p_supplierForest_node_081209 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081209 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081209 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076415 := by
  decide +kernel

theorem g32p_supplierForest_actual_081209 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081209) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_081209
    g32p_supplierForest_actual_076415

def g32p_supplierForest_node_081232 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_081232 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081232 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_019140 := by
  decide +kernel

theorem g32p_supplierForest_actual_081232 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081232) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_081232
    g32p_supplierForest_actual_019140

def g32p_supplierForest_node_081347 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081347 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081347 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073837 := by
  decide +kernel

theorem g32p_supplierForest_actual_081347 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081347) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 0 g32p_supplierForest_edge_081347
    g32p_supplierForest_actual_073837

def g32p_supplierForest_node_081480 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081480 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081480 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076511 := by
  decide +kernel

theorem g32p_supplierForest_actual_081480 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081480) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_081480
    g32p_supplierForest_actual_076511

def g32p_supplierForest_node_081490 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_081490 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081490 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022332 := by
  decide +kernel

theorem g32p_supplierForest_actual_081490 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081490) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_081490
    g32p_supplierForest_actual_022332

def g32p_supplierForest_node_081506 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_081506 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081506 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_019918 := by
  decide +kernel

theorem g32p_supplierForest_actual_081506 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081506) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_081506
    g32p_supplierForest_actual_019918

def g32p_supplierForest_node_081548 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_081548 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081548 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092695 := by
  decide +kernel

theorem g32p_supplierForest_actual_081548 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081548) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_081548
    g32p_supplierForest_actual_092695

def g32p_supplierForest_node_081595 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081595 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081595 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_019959 := by
  decide +kernel

theorem g32p_supplierForest_actual_081595 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081595) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 0 g32p_supplierForest_edge_081595
    g32p_supplierForest_actual_019959

def g32p_supplierForest_node_081640 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081640 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081640 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_018069 := by
  decide +kernel

theorem g32p_supplierForest_actual_081640 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081640) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_081640
    g32p_supplierForest_actual_018069

def g32p_supplierForest_node_081699 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_081699 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081699 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073341 := by
  decide +kernel

theorem g32p_supplierForest_actual_081699 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081699) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_081699
    g32p_supplierForest_actual_073341

def g32p_supplierForest_node_081718 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_081718 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081718 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_075139 := by
  decide +kernel

theorem g32p_supplierForest_actual_081718 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081718) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_081718
    g32p_supplierForest_actual_075139

def g32p_supplierForest_node_081728 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_081728 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081728 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_019918 := by
  decide +kernel

theorem g32p_supplierForest_actual_081728 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081728) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_081728
    g32p_supplierForest_actual_019918

def g32p_supplierForest_node_081772 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_081772 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081772 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092938 := by
  decide +kernel

theorem g32p_supplierForest_actual_081772 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081772) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_081772
    g32p_supplierForest_actual_092938

def g32p_supplierForest_node_081803 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_081803 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081803 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076729 := by
  decide +kernel

theorem g32p_supplierForest_actual_081803 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081803) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_081803
    g32p_supplierForest_actual_076729

def g32p_supplierForest_node_081809 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_081809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081809 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082666 := by
  decide +kernel

theorem g32p_supplierForest_actual_081809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081809) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_081809
    g32p_supplierForest_actual_082666

def g32p_supplierForest_node_081850 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_081850 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081850 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072028 := by
  decide +kernel

theorem g32p_supplierForest_actual_081850 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081850) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_081850
    g32p_supplierForest_actual_072028

def g32p_supplierForest_node_081895 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_081895 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081895 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082662 := by
  decide +kernel

theorem g32p_supplierForest_actual_081895 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081895) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 1 g32p_supplierForest_edge_081895
    g32p_supplierForest_actual_082662

def g32p_supplierForest_node_081896 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081896 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081896 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082666 := by
  decide +kernel

theorem g32p_supplierForest_actual_081896 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081896) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_081896
    g32p_supplierForest_actual_082666

def g32p_supplierForest_node_081972 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081972 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021802 := by
  decide +kernel

theorem g32p_supplierForest_actual_081972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081972) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_081972
    g32p_supplierForest_actual_021802

def g32p_supplierForest_node_081973 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_081973 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081973 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076834 := by
  decide +kernel

theorem g32p_supplierForest_actual_081973 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081973) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 1 g32p_supplierForest_edge_081973
    g32p_supplierForest_actual_076834

def g32p_supplierForest_node_082101 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082101 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082101 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022063 := by
  decide +kernel

theorem g32p_supplierForest_actual_082101 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082101) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_082101
    g32p_supplierForest_actual_022063

def g32p_supplierForest_node_082108 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_082108 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082108 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096068 := by
  decide +kernel

theorem g32p_supplierForest_actual_082108 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082108) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_082108
    g32p_supplierForest_actual_096068

def g32p_supplierForest_node_082128 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_082128 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082128 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014596 := by
  decide +kernel

theorem g32p_supplierForest_actual_082128 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082128) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_082128
    g32p_supplierForest_actual_014596

def g32p_supplierForest_node_082250 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_082250 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082250 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074188 := by
  decide +kernel

theorem g32p_supplierForest_actual_082250 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082250) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 0 g32p_supplierForest_edge_082250
    g32p_supplierForest_actual_074188

def g32p_supplierForest_node_082282 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_082282 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082282 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_020665 := by
  decide +kernel

theorem g32p_supplierForest_actual_082282 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082282) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_082282
    g32p_supplierForest_actual_020665

def g32p_supplierForest_node_082332 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_082332 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082332 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083267 := by
  decide +kernel

theorem g32p_supplierForest_actual_082332 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082332) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 1 g32p_supplierForest_edge_082332
    g32p_supplierForest_actual_083267

def g32p_supplierForest_node_082352 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082352 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082352 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083274 := by
  decide +kernel

theorem g32p_supplierForest_actual_082352 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082352) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 2 g32p_supplierForest_edge_082352
    g32p_supplierForest_actual_083274

def g32p_supplierForest_node_082362 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_082362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082362 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_082395 := by
  decide +kernel

theorem g32p_supplierForest_actual_082362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082362) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_082362
    g32p_supplierForest_actual_082395

def g32p_supplierForest_node_082390 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082390 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082390 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080546 := by
  decide +kernel

theorem g32p_supplierForest_actual_082390 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082390) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 1 g32p_supplierForest_edge_082390
    g32p_supplierForest_actual_080546

def g32p_supplierForest_node_082561 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082561 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082561 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_021304 := by
  decide +kernel

theorem g32p_supplierForest_actual_082561 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082561) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_082561
    g32p_supplierForest_actual_021304

def g32p_supplierForest_node_082569 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_082569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082569 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_017997 := by
  decide +kernel

theorem g32p_supplierForest_actual_082569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082569) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_082569
    g32p_supplierForest_actual_017997

def g32p_supplierForest_node_082596 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082596 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082596 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_090534 := by
  decide +kernel

theorem g32p_supplierForest_actual_082596 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082596) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_082596
    g32p_supplierForest_actual_090534

def g32p_supplierForest_node_082601 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082601 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082601 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_086038 := by
  decide +kernel

theorem g32p_supplierForest_actual_082601 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082601) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_082601
    g32p_supplierForest_actual_086038

def g32p_supplierForest_node_082631 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082631 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082631 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_023076 := by
  decide +kernel

theorem g32p_supplierForest_actual_082631 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082631) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 2 g32p_supplierForest_edge_082631
    g32p_supplierForest_actual_023076

def g32p_supplierForest_node_082665 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082665 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082665 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086621 := by
  decide +kernel

theorem g32p_supplierForest_actual_082665 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082665) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 2 g32p_supplierForest_edge_082665
    g32p_supplierForest_actual_086621

def g32p_supplierForest_node_082715 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082715 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097898 := by
  decide +kernel

theorem g32p_supplierForest_actual_082715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082715) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_082715
    g32p_supplierForest_actual_097898

def g32p_supplierForest_node_082747 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_082747 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082747 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080136 := by
  decide +kernel

theorem g32p_supplierForest_actual_082747 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082747) ∧
        IsConj g (g32p_literalRepresentative 82) := by
  exact g32p_archive_step_lift _ _ 82 1 g32p_supplierForest_edge_082747
    g32p_supplierForest_actual_080136

def g32p_supplierForest_node_082799 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082799 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082799 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018161 := by
  decide +kernel

theorem g32p_supplierForest_actual_082799 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082799) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_082799
    g32p_supplierForest_actual_018161

def g32p_supplierForest_node_082814 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_082814 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082814 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094922 := by
  decide +kernel

theorem g32p_supplierForest_actual_082814 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082814) ∧
        IsConj g (g32p_literalRepresentative 84) := by
  exact g32p_archive_step_lift _ _ 84 3 g32p_supplierForest_edge_082814
    g32p_supplierForest_actual_094922

def g32p_supplierForest_node_082837 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082837 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086002 := by
  decide +kernel

theorem g32p_supplierForest_actual_082837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082837) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_082837
    g32p_supplierForest_actual_086002

def g32p_supplierForest_node_082853 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082853 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_018627 := by
  decide +kernel

theorem g32p_supplierForest_actual_082853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082853) ∧
        IsConj g (g32p_literalRepresentative 13) := by
  exact g32p_archive_step_lift _ _ 13 0 g32p_supplierForest_edge_082853
    g32p_supplierForest_actual_018627

def g32p_supplierForest_node_082894 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082894 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082894 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_015994 := by
  decide +kernel

theorem g32p_supplierForest_actual_082894 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082894) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_082894
    g32p_supplierForest_actual_015994

def g32p_supplierForest_node_082952 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_082952 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082952 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_081174 := by
  decide +kernel

theorem g32p_supplierForest_actual_082952 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082952) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_082952
    g32p_supplierForest_actual_081174

def g32p_supplierForest_node_083025 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_083025 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083025 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_018722 := by
  decide +kernel

theorem g32p_supplierForest_actual_083025 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083025) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 0 g32p_supplierForest_edge_083025
    g32p_supplierForest_actual_018722

def g32p_supplierForest_node_083060 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_083060 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083060 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072722 := by
  decide +kernel

theorem g32p_supplierForest_actual_083060 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083060) ∧
        IsConj g (g32p_literalRepresentative 56) := by
  exact g32p_archive_step_lift _ _ 56 3 g32p_supplierForest_edge_083060
    g32p_supplierForest_actual_072722

end HodgeLean.Foundations.Program

end
end
