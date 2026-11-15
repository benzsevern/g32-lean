import HodgeLean.Foundations.Program.G32PropFourSixPacked0236
import HodgeLean.Foundations.Program.G32PropFourSixPacked0237
import HodgeLean.Foundations.Program.G32PropFourSixPacked0238
import HodgeLean.Foundations.Program.G32PropFourSixPacked0239
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0223
import HodgeLean.Foundations.Program.G32PropFourSixPacked0224
import HodgeLean.Foundations.Program.G32PropFourSixPacked0225
import HodgeLean.Foundations.Program.G32PropFourSixPacked0226
import HodgeLean.Foundations.Program.G32PropFourSixPacked0227
import HodgeLean.Foundations.Program.G32PropFourSixPacked0228
import HodgeLean.Foundations.Program.G32PropFourSixPacked0229

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_048 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_099018 else g32p_supplierForest_node_099024) else (if i.val < 3 then g32p_supplierForest_node_099041 else g32p_supplierForest_node_099104)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_099112 else g32p_supplierForest_node_099127) else (if i.val < 7 then g32p_supplierForest_node_099150 else g32p_supplierForest_node_099215))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_099389 else g32p_supplierForest_node_099464) else (if i.val < 11 then g32p_supplierForest_node_099466 else g32p_supplierForest_node_099490)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_099505 else g32p_supplierForest_node_099529) else (if i.val < 15 then g32p_supplierForest_node_099552 else g32p_supplierForest_node_099569)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_099596 else g32p_supplierForest_node_099606) else (if i.val < 19 then g32p_supplierForest_node_099765 else g32p_supplierForest_node_099766)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_099798 else g32p_supplierForest_node_099803) else (if i.val < 23 then g32p_supplierForest_node_099833 else g32p_supplierForest_node_099901))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_099918 else g32p_supplierForest_node_100010) else (if i.val < 27 then g32p_supplierForest_node_100027 else g32p_supplierForest_node_100059)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_100064 else g32p_supplierForest_node_100070) else (if i.val < 31 then g32p_supplierForest_node_100082 else g32p_supplierForest_node_100084))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_100095 else g32p_supplierForest_node_100118) else (if i.val < 35 then g32p_supplierForest_node_100195 else g32p_supplierForest_node_100207)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_100313 else g32p_supplierForest_node_100359) else (if i.val < 39 then g32p_supplierForest_node_100389 else g32p_supplierForest_node_100417))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_100425 else g32p_supplierForest_node_100482) else (if i.val < 43 then g32p_supplierForest_node_100583 else g32p_supplierForest_node_100611)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_100639 else g32p_supplierForest_node_100727) else (if i.val < 47 then g32p_supplierForest_node_100741 else g32p_supplierForest_node_100745)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_100887 else g32p_supplierForest_node_100898) else (if i.val < 51 then g32p_supplierForest_node_100924 else g32p_supplierForest_node_101148)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_101151 else g32p_supplierForest_node_101154) else (if i.val < 55 then g32p_supplierForest_node_101157 else g32p_supplierForest_node_101179))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_101217 else g32p_supplierForest_node_101218) else (if i.val < 59 then g32p_supplierForest_node_101220 else g32p_supplierForest_node_101255)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_101272 else g32p_supplierForest_node_101277) else (if i.val < 63 then g32p_supplierForest_node_101290 else g32p_supplierForest_node_101295)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_101318 else g32p_supplierForest_node_101320) else (if i.val < 67 then g32p_supplierForest_node_101331 else g32p_supplierForest_node_101372)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_101387 else g32p_supplierForest_node_101388) else (if i.val < 71 then g32p_supplierForest_node_101393 else g32p_supplierForest_node_101426))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_101431 else g32p_supplierForest_node_101433) else (if i.val < 75 then g32p_supplierForest_node_101483 else g32p_supplierForest_node_101502)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_101507 else g32p_supplierForest_node_101514) else (if i.val < 79 then g32p_supplierForest_node_101562 else g32p_supplierForest_node_101565)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_101576 else g32p_supplierForest_node_101586) else (if i.val < 83 then g32p_supplierForest_node_101628 else g32p_supplierForest_node_101638)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_101653 else g32p_supplierForest_node_101694) else (if i.val < 87 then g32p_supplierForest_node_101705 else g32p_supplierForest_node_101732))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_101737 else g32p_supplierForest_node_101799) else (if i.val < 91 then g32p_supplierForest_node_101836 else g32p_supplierForest_node_101853)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_101862 else g32p_supplierForest_node_101886) else (if i.val < 95 then g32p_supplierForest_node_101897 else g32p_supplierForest_node_101921))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_101941 else g32p_supplierForest_node_101943) else (if i.val < 99 then g32p_supplierForest_node_101959 else g32p_supplierForest_node_101984)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_102004 else g32p_supplierForest_node_102021) else (if i.val < 103 then g32p_supplierForest_node_102027 else g32p_supplierForest_node_102050))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_102070 else g32p_supplierForest_node_102086) else (if i.val < 107 then g32p_supplierForest_node_102088 else g32p_supplierForest_node_102111)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_102123 else g32p_supplierForest_node_102143) else (if i.val < 111 then g32p_supplierForest_node_102144 else g32p_supplierForest_node_102173)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_102185 else g32p_supplierForest_node_102197) else (if i.val < 115 then g32p_supplierForest_node_102207 else g32p_supplierForest_node_102251)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_102253 else g32p_supplierForest_node_102257) else (if i.val < 119 then g32p_supplierForest_node_102258 else g32p_supplierForest_node_102274))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_102336 else g32p_supplierForest_node_102352) else (if i.val < 123 then g32p_supplierForest_node_102373 else g32p_supplierForest_node_102378)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_102398 else g32p_supplierForest_node_102442) else (if i.val < 127 then g32p_supplierForest_node_102452 else g32p_supplierForest_node_102461))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_102467 else g32p_supplierForest_node_102472) else (if i.val < 131 then g32p_supplierForest_node_102481 else g32p_supplierForest_node_102482)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_102499 else g32p_supplierForest_node_102509) else (if i.val < 135 then g32p_supplierForest_node_102563 else g32p_supplierForest_node_102599))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_102607 else g32p_supplierForest_node_102628) else (if i.val < 139 then g32p_supplierForest_node_102691 else g32p_supplierForest_node_102708)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_102769 else g32p_supplierForest_node_102791) else (if i.val < 143 then g32p_supplierForest_node_102798 else g32p_supplierForest_node_102867)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_102874 else g32p_supplierForest_node_102890) else (if i.val < 147 then g32p_supplierForest_node_102895 else g32p_supplierForest_node_102958)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_102972 else g32p_supplierForest_node_103009) else (if i.val < 151 then g32p_supplierForest_node_103027 else g32p_supplierForest_node_103035))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_103054 else g32p_supplierForest_node_103055) else (if i.val < 155 then g32p_supplierForest_node_103068 else g32p_supplierForest_node_103090)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_103102 else g32p_supplierForest_node_103142) else (if i.val < 159 then g32p_supplierForest_node_103150 else g32p_supplierForest_node_103168))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_103171 else g32p_supplierForest_node_103172) else (if i.val < 163 then g32p_supplierForest_node_103181 else g32p_supplierForest_node_103198)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_103213 else g32p_supplierForest_node_103242) else (if i.val < 167 then g32p_supplierForest_node_103248 else g32p_supplierForest_node_103294))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_103302 else g32p_supplierForest_node_103313) else (if i.val < 171 then g32p_supplierForest_node_103316 else g32p_supplierForest_node_103347)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_103363 else g32p_supplierForest_node_103398) else (if i.val < 175 then g32p_supplierForest_node_103432 else g32p_supplierForest_node_103460)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_103498 else g32p_supplierForest_node_103539) else (if i.val < 179 then g32p_supplierForest_node_103540 else g32p_supplierForest_node_103569)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_103573 else g32p_supplierForest_node_103601) else (if i.val < 183 then g32p_supplierForest_node_103614 else g32p_supplierForest_node_103620))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_103646 else g32p_supplierForest_node_103664) else (if i.val < 187 then g32p_supplierForest_node_103688 else g32p_supplierForest_node_103693)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_103710 else g32p_supplierForest_node_103784) else (if i.val < 191 then g32p_supplierForest_node_103807 else g32p_supplierForest_node_103811)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_103846 else g32p_supplierForest_node_103886) else (if i.val < 195 then g32p_supplierForest_node_103890 else g32p_supplierForest_node_103923)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_103969 else g32p_supplierForest_node_104018) else (if i.val < 199 then g32p_supplierForest_node_104020 else g32p_supplierForest_node_104027))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_104066 else g32p_supplierForest_node_104075) else (if i.val < 203 then g32p_supplierForest_node_104124 else g32p_supplierForest_node_104139)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_104169 else g32p_supplierForest_node_104183) else (if i.val < 207 then g32p_supplierForest_node_104208 else g32p_supplierForest_node_104225)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_104260 else g32p_supplierForest_node_104273) else (if i.val < 211 then g32p_supplierForest_node_104277 else g32p_supplierForest_node_104292)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_104300 else g32p_supplierForest_node_104310) else (if i.val < 215 then g32p_supplierForest_node_104328 else g32p_supplierForest_node_104331))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_104341 else g32p_supplierForest_node_104373) else (if i.val < 219 then g32p_supplierForest_node_104404 else g32p_supplierForest_node_104421)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_104428 else g32p_supplierForest_node_104483) else (if i.val < 223 then g32p_supplierForest_node_104539 else g32p_supplierForest_node_104556))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_104576 else g32p_supplierForest_node_104580) else (if i.val < 227 then g32p_supplierForest_node_104618 else g32p_supplierForest_node_104642)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_104648 else g32p_supplierForest_node_104659) else (if i.val < 231 then g32p_supplierForest_node_104692 else g32p_supplierForest_node_104740))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_104748 else g32p_supplierForest_node_104807) else (if i.val < 235 then g32p_supplierForest_node_104808 else g32p_supplierForest_node_104813)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_104823 else g32p_supplierForest_node_104825) else (if i.val < 239 then g32p_supplierForest_node_104883 else g32p_supplierForest_node_104898)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_104899 else g32p_supplierForest_node_104910) else (if i.val < 243 then g32p_supplierForest_node_104919 else g32p_supplierForest_node_104958)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_105012 else g32p_supplierForest_node_105030) else (if i.val < 247 then g32p_supplierForest_node_105032 else g32p_supplierForest_node_105043))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_105062 else g32p_supplierForest_node_105067) else (if i.val < 251 then g32p_supplierForest_node_105069 else g32p_supplierForest_node_105076)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_105077 else g32p_supplierForest_node_105079) else (if i.val < 255 then g32p_supplierForest_node_105081 else g32p_supplierForest_node_105134))))))))

def g32p_supplierForest_classes_048 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 52 else 86) else (if i.val < 3 then 47 else 13)) else (if i.val < 6 then (if i.val < 5 then 53 else 26) else (if i.val < 7 then 11 else 45))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 47 else 45) else (if i.val < 11 then 84 else 11)) else (if i.val < 14 then (if i.val < 13 then 86 else 54) else (if i.val < 15 then 55 else 49)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 55 else 80) else (if i.val < 19 then 49 else 52)) else (if i.val < 22 then (if i.val < 21 then 80 else 13) else (if i.val < 23 then 26 else 25))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 11 else 26) else (if i.val < 27 then 47 else 52)) else (if i.val < 30 then (if i.val < 29 then 86 else 26) else (if i.val < 31 then 86 else 26))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 11 else 54) else (if i.val < 35 then 45 else 52)) else (if i.val < 38 then (if i.val < 37 then 86 else 49) else (if i.val < 39 then 45 else 80))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 26 else 86) else (if i.val < 43 then 82 else 80)) else (if i.val < 46 then (if i.val < 45 then 49 else 54) else (if i.val < 47 then 46 else 12)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 25 else 55) else (if i.val < 51 then 46 else 54)) else (if i.val < 54 then (if i.val < 53 then 56 else 47) else (if i.val < 55 then 27 else 51))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 50 else 80) else (if i.val < 59 then 49 else 25)) else (if i.val < 62 then (if i.val < 61 then 46 else 54) else (if i.val < 63 then 52 else 13)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 13) else (if i.val < 67 then 50 else 80)) else (if i.val < 70 then (if i.val < 69 then 85 else 85) else (if i.val < 71 then 13 else 52))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 52 else 52) else (if i.val < 75 then 50 else 55)) else (if i.val < 78 then (if i.val < 77 then 13 else 13) else (if i.val < 79 then 53 else 9)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 47 else 54) else (if i.val < 83 then 46 else 46)) else (if i.val < 86 then (if i.val < 85 then 81 else 25) else (if i.val < 87 then 26 else 84))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 55 else 49) else (if i.val < 91 then 80 else 25)) else (if i.val < 94 then (if i.val < 93 then 46 else 25) else (if i.val < 95 then 59 else 57))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 66 else 16) else (if i.val < 99 then 57 else 57)) else (if i.val < 102 then (if i.val < 101 then 57 else 33) else (if i.val < 103 then 59 else 30))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 59 else 60) else (if i.val < 107 then 57 else 62)) else (if i.val < 110 then (if i.val < 109 then 57 else 30) else (if i.val < 111 then 66 else 57)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 66 else 33) else (if i.val < 115 then 60 else 57)) else (if i.val < 118 then (if i.val < 117 then 34 else 63) else (if i.val < 119 then 60 else 59))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 59 else 14) else (if i.val < 123 then 61 else 66)) else (if i.val < 126 then (if i.val < 125 then 66 else 66) else (if i.val < 127 then 64 else 63))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 59 else 59) else (if i.val < 131 then 65 else 58)) else (if i.val < 134 then (if i.val < 133 then 61 else 57) else (if i.val < 135 then 60 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 58 else 59) else (if i.val < 139 then 63 else 30)) else (if i.val < 142 then (if i.val < 141 then 57 else 32) else (if i.val < 143 then 29 else 64)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 66 else 62) else (if i.val < 147 then 62 else 58)) else (if i.val < 150 then (if i.val < 149 then 60 else 59) else (if i.val < 151 then 4 else 63))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 4 else 17) else (if i.val < 155 then 34 else 57)) else (if i.val < 158 then (if i.val < 157 then 60 else 65) else (if i.val < 159 then 36 else 36))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 63 else 61) else (if i.val < 163 then 57 else 57)) else (if i.val < 166 then (if i.val < 165 then 63 else 30) else (if i.val < 167 then 4 else 30))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 4 else 58) else (if i.val < 171 then 61 else 60)) else (if i.val < 174 then (if i.val < 173 then 16 else 30) else (if i.val < 175 then 29 else 62)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 30 else 66) else (if i.val < 179 then 66 else 60)) else (if i.val < 182 then (if i.val < 181 then 29 else 63) else (if i.val < 183 then 29 else 63))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 30 else 35) else (if i.val < 187 then 60 else 30)) else (if i.val < 190 then (if i.val < 189 then 57 else 59) else (if i.val < 191 then 58 else 34)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 30 else 29) else (if i.val < 195 then 64 else 66)) else (if i.val < 198 then (if i.val < 197 then 65 else 34) else (if i.val < 199 then 57 else 60))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 61 else 15) else (if i.val < 203 then 59 else 60)) else (if i.val < 206 then (if i.val < 205 then 60 else 60) else (if i.val < 207 then 36 else 17)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 30 else 57) else (if i.val < 211 then 33 else 30)) else (if i.val < 214 then (if i.val < 213 then 36 else 16) else (if i.val < 215 then 17 else 15))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 30 else 60) else (if i.val < 219 then 29 else 57)) else (if i.val < 222 then (if i.val < 221 then 14 else 30) else (if i.val < 223 then 60 else 32))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 30 else 60) else (if i.val < 227 then 30 else 63)) else (if i.val < 230 then (if i.val < 229 then 57 else 60) else (if i.val < 231 then 4 else 36))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 57 else 33) else (if i.val < 235 then 60 else 29)) else (if i.val < 238 then (if i.val < 237 then 35 else 35) else (if i.val < 239 then 29 else 60)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 30 else 33) else (if i.val < 243 then 30 else 30)) else (if i.val < 246 then (if i.val < 245 then 60 else 35) else (if i.val < 247 then 60 else 30))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 35 else 57) else (if i.val < 251 then 59 else 59)) else (if i.val < 254 then (if i.val < 253 then 63 else 63) else (if i.val < 255 then 34 else 59))))))))

theorem g32p_supplierForest_actual_048 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_048 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_048 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_099018
  · exact g32p_supplierForest_actual_099024
  · exact g32p_supplierForest_actual_099041
  · exact g32p_supplierForest_actual_099104
  · exact g32p_supplierForest_actual_099112
  · exact g32p_supplierForest_actual_099127
  · exact g32p_supplierForest_actual_099150
  · exact g32p_supplierForest_actual_099215
  · exact g32p_supplierForest_actual_099389
  · exact g32p_supplierForest_actual_099464
  · exact g32p_supplierForest_actual_099466
  · exact g32p_supplierForest_actual_099490
  · exact g32p_supplierForest_actual_099505
  · exact g32p_supplierForest_actual_099529
  · exact g32p_supplierForest_actual_099552
  · exact g32p_supplierForest_actual_099569
  · exact g32p_supplierForest_actual_099596
  · exact g32p_supplierForest_actual_099606
  · exact g32p_supplierForest_actual_099765
  · exact g32p_supplierForest_actual_099766
  · exact g32p_supplierForest_actual_099798
  · exact g32p_supplierForest_actual_099803
  · exact g32p_supplierForest_actual_099833
  · exact g32p_supplierForest_actual_099901
  · exact g32p_supplierForest_actual_099918
  · exact g32p_supplierForest_actual_100010
  · exact g32p_supplierForest_actual_100027
  · exact g32p_supplierForest_actual_100059
  · exact g32p_supplierForest_actual_100064
  · exact g32p_supplierForest_actual_100070
  · exact g32p_supplierForest_actual_100082
  · exact g32p_supplierForest_actual_100084
  · exact g32p_supplierForest_actual_100095
  · exact g32p_supplierForest_actual_100118
  · exact g32p_supplierForest_actual_100195
  · exact g32p_supplierForest_actual_100207
  · exact g32p_supplierForest_actual_100313
  · exact g32p_supplierForest_actual_100359
  · exact g32p_supplierForest_actual_100389
  · exact g32p_supplierForest_actual_100417
  · exact g32p_supplierForest_actual_100425
  · exact g32p_supplierForest_actual_100482
  · exact g32p_supplierForest_actual_100583
  · exact g32p_supplierForest_actual_100611
  · exact g32p_supplierForest_actual_100639
  · exact g32p_supplierForest_actual_100727
  · exact g32p_supplierForest_actual_100741
  · exact g32p_supplierForest_actual_100745
  · exact g32p_supplierForest_actual_100887
  · exact g32p_supplierForest_actual_100898
  · exact g32p_supplierForest_actual_100924
  · exact g32p_supplierForest_actual_101148
  · exact g32p_supplierForest_actual_101151
  · exact g32p_supplierForest_actual_101154
  · exact g32p_supplierForest_actual_101157
  · exact g32p_supplierForest_actual_101179
  · exact g32p_supplierForest_actual_101217
  · exact g32p_supplierForest_actual_101218
  · exact g32p_supplierForest_actual_101220
  · exact g32p_supplierForest_actual_101255
  · exact g32p_supplierForest_actual_101272
  · exact g32p_supplierForest_actual_101277
  · exact g32p_supplierForest_actual_101290
  · exact g32p_supplierForest_actual_101295
  · exact g32p_supplierForest_actual_101318
  · exact g32p_supplierForest_actual_101320
  · exact g32p_supplierForest_actual_101331
  · exact g32p_supplierForest_actual_101372
  · exact g32p_supplierForest_actual_101387
  · exact g32p_supplierForest_actual_101388
  · exact g32p_supplierForest_actual_101393
  · exact g32p_supplierForest_actual_101426
  · exact g32p_supplierForest_actual_101431
  · exact g32p_supplierForest_actual_101433
  · exact g32p_supplierForest_actual_101483
  · exact g32p_supplierForest_actual_101502
  · exact g32p_supplierForest_actual_101507
  · exact g32p_supplierForest_actual_101514
  · exact g32p_supplierForest_actual_101562
  · exact g32p_supplierForest_actual_101565
  · exact g32p_supplierForest_actual_101576
  · exact g32p_supplierForest_actual_101586
  · exact g32p_supplierForest_actual_101628
  · exact g32p_supplierForest_actual_101638
  · exact g32p_supplierForest_actual_101653
  · exact g32p_supplierForest_actual_101694
  · exact g32p_supplierForest_actual_101705
  · exact g32p_supplierForest_actual_101732
  · exact g32p_supplierForest_actual_101737
  · exact g32p_supplierForest_actual_101799
  · exact g32p_supplierForest_actual_101836
  · exact g32p_supplierForest_actual_101853
  · exact g32p_supplierForest_actual_101862
  · exact g32p_supplierForest_actual_101886
  · exact g32p_supplierForest_actual_101897
  · exact g32p_supplierForest_actual_101921
  · exact g32p_supplierForest_actual_101941
  · exact g32p_supplierForest_actual_101943
  · exact g32p_supplierForest_actual_101959
  · exact g32p_supplierForest_actual_101984
  · exact g32p_supplierForest_actual_102004
  · exact g32p_supplierForest_actual_102021
  · exact g32p_supplierForest_actual_102027
  · exact g32p_supplierForest_actual_102050
  · exact g32p_supplierForest_actual_102070
  · exact g32p_supplierForest_actual_102086
  · exact g32p_supplierForest_actual_102088
  · exact g32p_supplierForest_actual_102111
  · exact g32p_supplierForest_actual_102123
  · exact g32p_supplierForest_actual_102143
  · exact g32p_supplierForest_actual_102144
  · exact g32p_supplierForest_actual_102173
  · exact g32p_supplierForest_actual_102185
  · exact g32p_supplierForest_actual_102197
  · exact g32p_supplierForest_actual_102207
  · exact g32p_supplierForest_actual_102251
  · exact g32p_supplierForest_actual_102253
  · exact g32p_supplierForest_actual_102257
  · exact g32p_supplierForest_actual_102258
  · exact g32p_supplierForest_actual_102274
  · exact g32p_supplierForest_actual_102336
  · exact g32p_supplierForest_actual_102352
  · exact g32p_supplierForest_actual_102373
  · exact g32p_supplierForest_actual_102378
  · exact g32p_supplierForest_actual_102398
  · exact g32p_supplierForest_actual_102442
  · exact g32p_supplierForest_actual_102452
  · exact g32p_supplierForest_actual_102461
  · exact g32p_supplierForest_actual_102467
  · exact g32p_supplierForest_actual_102472
  · exact g32p_supplierForest_actual_102481
  · exact g32p_supplierForest_actual_102482
  · exact g32p_supplierForest_actual_102499
  · exact g32p_supplierForest_actual_102509
  · exact g32p_supplierForest_actual_102563
  · exact g32p_supplierForest_actual_102599
  · exact g32p_supplierForest_actual_102607
  · exact g32p_supplierForest_actual_102628
  · exact g32p_supplierForest_actual_102691
  · exact g32p_supplierForest_actual_102708
  · exact g32p_supplierForest_actual_102769
  · exact g32p_supplierForest_actual_102791
  · exact g32p_supplierForest_actual_102798
  · exact g32p_supplierForest_actual_102867
  · exact g32p_supplierForest_actual_102874
  · exact g32p_supplierForest_actual_102890
  · exact g32p_supplierForest_actual_102895
  · exact g32p_supplierForest_actual_102958
  · exact g32p_supplierForest_actual_102972
  · exact g32p_supplierForest_actual_103009
  · exact g32p_supplierForest_actual_103027
  · exact g32p_supplierForest_actual_103035
  · exact g32p_supplierForest_actual_103054
  · exact g32p_supplierForest_actual_103055
  · exact g32p_supplierForest_actual_103068
  · exact g32p_supplierForest_actual_103090
  · exact g32p_supplierForest_actual_103102
  · exact g32p_supplierForest_actual_103142
  · exact g32p_supplierForest_actual_103150
  · exact g32p_supplierForest_actual_103168
  · exact g32p_supplierForest_actual_103171
  · exact g32p_supplierForest_actual_103172
  · exact g32p_supplierForest_actual_103181
  · exact g32p_supplierForest_actual_103198
  · exact g32p_supplierForest_actual_103213
  · exact g32p_supplierForest_actual_103242
  · exact g32p_supplierForest_actual_103248
  · exact g32p_supplierForest_actual_103294
  · exact g32p_supplierForest_actual_103302
  · exact g32p_supplierForest_actual_103313
  · exact g32p_supplierForest_actual_103316
  · exact g32p_supplierForest_actual_103347
  · exact g32p_supplierForest_actual_103363
  · exact g32p_supplierForest_actual_103398
  · exact g32p_supplierForest_actual_103432
  · exact g32p_supplierForest_actual_103460
  · exact g32p_supplierForest_actual_103498
  · exact g32p_supplierForest_actual_103539
  · exact g32p_supplierForest_actual_103540
  · exact g32p_supplierForest_actual_103569
  · exact g32p_supplierForest_actual_103573
  · exact g32p_supplierForest_actual_103601
  · exact g32p_supplierForest_actual_103614
  · exact g32p_supplierForest_actual_103620
  · exact g32p_supplierForest_actual_103646
  · exact g32p_supplierForest_actual_103664
  · exact g32p_supplierForest_actual_103688
  · exact g32p_supplierForest_actual_103693
  · exact g32p_supplierForest_actual_103710
  · exact g32p_supplierForest_actual_103784
  · exact g32p_supplierForest_actual_103807
  · exact g32p_supplierForest_actual_103811
  · exact g32p_supplierForest_actual_103846
  · exact g32p_supplierForest_actual_103886
  · exact g32p_supplierForest_actual_103890
  · exact g32p_supplierForest_actual_103923
  · exact g32p_supplierForest_actual_103969
  · exact g32p_supplierForest_actual_104018
  · exact g32p_supplierForest_actual_104020
  · exact g32p_supplierForest_actual_104027
  · exact g32p_supplierForest_actual_104066
  · exact g32p_supplierForest_actual_104075
  · exact g32p_supplierForest_actual_104124
  · exact g32p_supplierForest_actual_104139
  · exact g32p_supplierForest_actual_104169
  · exact g32p_supplierForest_actual_104183
  · exact g32p_supplierForest_actual_104208
  · exact g32p_supplierForest_actual_104225
  · exact g32p_supplierForest_actual_104260
  · exact g32p_supplierForest_actual_104273
  · exact g32p_supplierForest_actual_104277
  · exact g32p_supplierForest_actual_104292
  · exact g32p_supplierForest_actual_104300
  · exact g32p_supplierForest_actual_104310
  · exact g32p_supplierForest_actual_104328
  · exact g32p_supplierForest_actual_104331
  · exact g32p_supplierForest_actual_104341
  · exact g32p_supplierForest_actual_104373
  · exact g32p_supplierForest_actual_104404
  · exact g32p_supplierForest_actual_104421
  · exact g32p_supplierForest_actual_104428
  · exact g32p_supplierForest_actual_104483
  · exact g32p_supplierForest_actual_104539
  · exact g32p_supplierForest_actual_104556
  · exact g32p_supplierForest_actual_104576
  · exact g32p_supplierForest_actual_104580
  · exact g32p_supplierForest_actual_104618
  · exact g32p_supplierForest_actual_104642
  · exact g32p_supplierForest_actual_104648
  · exact g32p_supplierForest_actual_104659
  · exact g32p_supplierForest_actual_104692
  · exact g32p_supplierForest_actual_104740
  · exact g32p_supplierForest_actual_104748
  · exact g32p_supplierForest_actual_104807
  · exact g32p_supplierForest_actual_104808
  · exact g32p_supplierForest_actual_104813
  · exact g32p_supplierForest_actual_104823
  · exact g32p_supplierForest_actual_104825
  · exact g32p_supplierForest_actual_104883
  · exact g32p_supplierForest_actual_104898
  · exact g32p_supplierForest_actual_104899
  · exact g32p_supplierForest_actual_104910
  · exact g32p_supplierForest_actual_104919
  · exact g32p_supplierForest_actual_104958
  · exact g32p_supplierForest_actual_105012
  · exact g32p_supplierForest_actual_105030
  · exact g32p_supplierForest_actual_105032
  · exact g32p_supplierForest_actual_105043
  · exact g32p_supplierForest_actual_105062
  · exact g32p_supplierForest_actual_105067
  · exact g32p_supplierForest_actual_105069
  · exact g32p_supplierForest_actual_105076
  · exact g32p_supplierForest_actual_105077
  · exact g32p_supplierForest_actual_105079
  · exact g32p_supplierForest_actual_105081
  · exact g32p_supplierForest_actual_105134

def g32p_supplierForest_nodes_049 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_105146 else g32p_supplierForest_node_105158) else (if i.val < 3 then g32p_supplierForest_node_105167 else g32p_supplierForest_node_105168)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_105226 else g32p_supplierForest_node_105230) else (if i.val < 7 then g32p_supplierForest_node_105234 else g32p_supplierForest_node_105275))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_105322 else g32p_supplierForest_node_105349) else (if i.val < 11 then g32p_supplierForest_node_105353 else g32p_supplierForest_node_105383)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_105419 else g32p_supplierForest_node_105463) else (if i.val < 15 then g32p_supplierForest_node_105464 else g32p_supplierForest_node_105507)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_105525 else g32p_supplierForest_node_105529) else (if i.val < 19 then g32p_supplierForest_node_105550 else g32p_supplierForest_node_105615)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_105633 else g32p_supplierForest_node_105666) else (if i.val < 23 then g32p_supplierForest_node_105726 else g32p_supplierForest_node_105772))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_105777 else g32p_supplierForest_node_105816) else (if i.val < 27 then g32p_supplierForest_node_105825 else g32p_supplierForest_node_105874)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_105888 else g32p_supplierForest_node_105970) else (if i.val < 31 then g32p_supplierForest_node_106072 else g32p_supplierForest_node_106143))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_106162 else g32p_supplierForest_node_106172) else (if i.val < 35 then g32p_supplierForest_node_106198 else g32p_supplierForest_node_106218)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_106229 else g32p_supplierForest_node_106239) else (if i.val < 39 then g32p_supplierForest_node_106301 else g32p_supplierForest_node_106306))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_106313 else g32p_supplierForest_node_106325) else (if i.val < 43 then g32p_supplierForest_node_106353 else g32p_supplierForest_node_106357)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_106376 else g32p_supplierForest_node_106414) else (if i.val < 47 then g32p_supplierForest_node_106419 else g32p_supplierForest_node_106425)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_106440 else g32p_supplierForest_node_106443) else (if i.val < 51 then g32p_supplierForest_node_106444 else g32p_supplierForest_node_106450)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_106482 else g32p_supplierForest_node_106491) else (if i.val < 55 then g32p_supplierForest_node_106521 else g32p_supplierForest_node_106544))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_106563 else g32p_supplierForest_node_106578) else (if i.val < 59 then g32p_supplierForest_node_106590 else g32p_supplierForest_node_106605)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_106614 else g32p_supplierForest_node_106633) else (if i.val < 63 then g32p_supplierForest_node_106654 else g32p_supplierForest_node_106686)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_106715 else g32p_supplierForest_node_106732) else (if i.val < 67 then g32p_supplierForest_node_106764 else g32p_supplierForest_node_106766)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_106807 else g32p_supplierForest_node_106816) else (if i.val < 71 then g32p_supplierForest_node_106889 else g32p_supplierForest_node_106895))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_106901 else g32p_supplierForest_node_106935) else (if i.val < 75 then g32p_supplierForest_node_106963 else g32p_supplierForest_node_107015)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_107024 else g32p_supplierForest_node_107028) else (if i.val < 79 then g32p_supplierForest_node_107029 else g32p_supplierForest_node_107033)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_107058 else g32p_supplierForest_node_107104) else (if i.val < 83 then g32p_supplierForest_node_107125 else g32p_supplierForest_node_107166)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_107258 else g32p_supplierForest_node_107259) else (if i.val < 87 then g32p_supplierForest_node_107278 else g32p_supplierForest_node_107305))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_107316 else g32p_supplierForest_node_107356) else (if i.val < 91 then g32p_supplierForest_node_107372 else g32p_supplierForest_node_107469)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_107500 else g32p_supplierForest_node_107509) else (if i.val < 95 then g32p_supplierForest_node_107516 else g32p_supplierForest_node_107524))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_107540 else g32p_supplierForest_node_107552) else (if i.val < 99 then g32p_supplierForest_node_107580 else g32p_supplierForest_node_107583)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_107585 else g32p_supplierForest_node_107590) else (if i.val < 103 then g32p_supplierForest_node_107595 else g32p_supplierForest_node_107628))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_107671 else g32p_supplierForest_node_107704) else (if i.val < 107 then g32p_supplierForest_node_107710 else g32p_supplierForest_node_107724)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_107762 else g32p_supplierForest_node_107777) else (if i.val < 111 then g32p_supplierForest_node_107800 else g32p_supplierForest_node_107818)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_107837 else g32p_supplierForest_node_107849) else (if i.val < 115 then g32p_supplierForest_node_107873 else g32p_supplierForest_node_107918)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_107922 else g32p_supplierForest_node_107984) else (if i.val < 119 then g32p_supplierForest_node_107996 else g32p_supplierForest_node_108030))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_108051 else g32p_supplierForest_node_108058) else (if i.val < 123 then g32p_supplierForest_node_108107 else g32p_supplierForest_node_108121)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_108124 else g32p_supplierForest_node_108126) else (if i.val < 127 then g32p_supplierForest_node_108134 else g32p_supplierForest_node_108145))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_108166 else g32p_supplierForest_node_108172) else (if i.val < 131 then g32p_supplierForest_node_108181 else g32p_supplierForest_node_108198)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_108204 else g32p_supplierForest_node_108223) else (if i.val < 135 then g32p_supplierForest_node_108238 else g32p_supplierForest_node_108258))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_108283 else g32p_supplierForest_node_108295) else (if i.val < 139 then g32p_supplierForest_node_108316 else g32p_supplierForest_node_108324)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_108398 else g32p_supplierForest_node_108416) else (if i.val < 143 then g32p_supplierForest_node_108417 else g32p_supplierForest_node_108457)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_108462 else g32p_supplierForest_node_108491) else (if i.val < 147 then g32p_supplierForest_node_108512 else g32p_supplierForest_node_108521)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_108546 else g32p_supplierForest_node_108558) else (if i.val < 151 then g32p_supplierForest_node_108579 else g32p_supplierForest_node_108587))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_108604 else g32p_supplierForest_node_108677) else (if i.val < 155 then g32p_supplierForest_node_108721 else g32p_supplierForest_node_108744)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_108751 else g32p_supplierForest_node_108764) else (if i.val < 159 then g32p_supplierForest_node_108779 else g32p_supplierForest_node_108806))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_108843 else g32p_supplierForest_node_108864) else (if i.val < 163 then g32p_supplierForest_node_108865 else g32p_supplierForest_node_108870)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_108894 else g32p_supplierForest_node_109009) else (if i.val < 167 then g32p_supplierForest_node_109013 else g32p_supplierForest_node_109032))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_109042 else g32p_supplierForest_node_109096) else (if i.val < 171 then g32p_supplierForest_node_109116 else g32p_supplierForest_node_109123)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_109128 else g32p_supplierForest_node_109132) else (if i.val < 175 then g32p_supplierForest_node_109196 else g32p_supplierForest_node_109197)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_109210 else g32p_supplierForest_node_109220) else (if i.val < 179 then g32p_supplierForest_node_109232 else g32p_supplierForest_node_109286)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_109300 else g32p_supplierForest_node_109306) else (if i.val < 183 then g32p_supplierForest_node_109312 else g32p_supplierForest_node_109320))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_109332 else g32p_supplierForest_node_109361) else (if i.val < 187 then g32p_supplierForest_node_109376 else g32p_supplierForest_node_109447)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_109471 else g32p_supplierForest_node_109501) else (if i.val < 191 then g32p_supplierForest_node_109506 else g32p_supplierForest_node_109599)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_109645 else g32p_supplierForest_node_109649) else (if i.val < 195 then g32p_supplierForest_node_109737 else g32p_supplierForest_node_109784)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_109803 else g32p_supplierForest_node_109853) else (if i.val < 199 then g32p_supplierForest_node_109870 else g32p_supplierForest_node_109903))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_109912 else g32p_supplierForest_node_109981) else (if i.val < 203 then g32p_supplierForest_node_109996 else g32p_supplierForest_node_110003)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_110011 else g32p_supplierForest_node_110045) else (if i.val < 207 then g32p_supplierForest_node_110050 else g32p_supplierForest_node_110059)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_110072 else g32p_supplierForest_node_110115) else (if i.val < 211 then g32p_supplierForest_node_110190 else g32p_supplierForest_node_110199)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_110220 else g32p_supplierForest_node_110268) else (if i.val < 215 then g32p_supplierForest_node_110345 else g32p_supplierForest_node_110383))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_110393 else g32p_supplierForest_node_110443) else (if i.val < 219 then g32p_supplierForest_node_110448 else g32p_supplierForest_node_110491)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_110504 else g32p_supplierForest_node_110521) else (if i.val < 223 then g32p_supplierForest_node_110550 else g32p_supplierForest_node_110591))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_110619 else g32p_supplierForest_node_110659) else (if i.val < 227 then g32p_supplierForest_node_110676 else g32p_supplierForest_node_110680)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_110700 else g32p_supplierForest_node_110725) else (if i.val < 231 then g32p_supplierForest_node_110733 else g32p_supplierForest_node_110756))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_110768 else g32p_supplierForest_node_110783) else (if i.val < 235 then g32p_supplierForest_node_110804 else g32p_supplierForest_node_110806)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_110820 else g32p_supplierForest_node_110831) else (if i.val < 239 then g32p_supplierForest_node_110854 else g32p_supplierForest_node_110914)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_110927 else g32p_supplierForest_node_110944) else (if i.val < 243 then g32p_supplierForest_node_110967 else g32p_supplierForest_node_110977)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_111012 else g32p_supplierForest_node_111014) else (if i.val < 247 then g32p_supplierForest_node_111166 else g32p_supplierForest_node_111184))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_111205 else g32p_supplierForest_node_111277) else (if i.val < 251 then g32p_supplierForest_node_111305 else g32p_supplierForest_node_111310)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_111311 else g32p_supplierForest_node_111475) else (if i.val < 255 then g32p_supplierForest_node_111514 else g32p_supplierForest_node_111534))))))))

def g32p_supplierForest_classes_049 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 60) else (if i.val < 3 then 61 else 60)) else (if i.val < 6 then (if i.val < 5 then 57 else 16) else (if i.val < 7 then 36 else 58))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 29) else (if i.val < 11 then 4 else 30)) else (if i.val < 14 then (if i.val < 13 then 34 else 62) else (if i.val < 15 then 36 else 63)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 63) else (if i.val < 19 then 59 else 16)) else (if i.val < 22 then (if i.val < 21 then 14 else 35) else (if i.val < 23 then 60 else 15))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 33 else 91) else (if i.val < 27 then 90 else 60)) else (if i.val < 30 then (if i.val < 29 then 30 else 32) else (if i.val < 31 then 30 else 33))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 89 else 60) else (if i.val < 35 then 92 else 33)) else (if i.val < 38 then (if i.val < 37 then 29 else 35) else (if i.val < 39 then 33 else 60))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 30 else 16) else (if i.val < 43 then 59 else 34)) else (if i.val < 46 then (if i.val < 45 then 29 else 36) else (if i.val < 47 then 29 else 63)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 14 else 60) else (if i.val < 51 then 59 else 29)) else (if i.val < 54 then (if i.val < 53 then 17 else 34) else (if i.val < 55 then 29 else 34))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 15 else 63) else (if i.val < 59 then 29 else 4)) else (if i.val < 62 then (if i.val < 61 then 29 else 16) else (if i.val < 63 then 29 else 63)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 91 else 57) else (if i.val < 67 then 66 else 36)) else (if i.val < 70 then (if i.val < 69 then 64 else 88) else (if i.val < 71 then 60 else 35))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 3 else 60) else (if i.val < 75 then 29 else 90)) else (if i.val < 78 then (if i.val < 77 then 33 else 36) else (if i.val < 79 then 17 else 58)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 16 else 61) else (if i.val < 83 then 29 else 58)) else (if i.val < 86 then (if i.val < 85 then 30 else 30) else (if i.val < 87 then 59 else 65))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 15 else 57) else (if i.val < 91 then 36 else 92)) else (if i.val < 94 then (if i.val < 93 then 66 else 29) else (if i.val < 95 then 59 else 66))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 61 else 16) else (if i.val < 99 then 14 else 34)) else (if i.val < 102 then (if i.val < 101 then 14 else 33) else (if i.val < 103 then 88 else 15))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 60 else 57) else (if i.val < 107 then 59 else 66)) else (if i.val < 110 then (if i.val < 109 then 61 else 89) else (if i.val < 111 then 93 else 61)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 66 else 65) else (if i.val < 115 then 59 else 90)) else (if i.val < 118 then (if i.val < 117 then 92 else 58) else (if i.val < 119 then 59 else 29))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 57 else 66) else (if i.val < 123 then 66 else 57)) else (if i.val < 126 then (if i.val < 125 then 59 else 60) else (if i.val < 127 then 16 else 16))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 57 else 59) else (if i.val < 131 then 35 else 30)) else (if i.val < 134 then (if i.val < 133 then 36 else 66) else (if i.val < 135 then 31 else 30))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 29 else 35) else (if i.val < 139 then 60 else 30)) else (if i.val < 142 then (if i.val < 141 then 17 else 91) else (if i.val < 143 then 92 else 59)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 59 else 91) else (if i.val < 147 then 59 else 57)) else (if i.val < 150 then (if i.val < 149 then 57 else 60) else (if i.val < 151 then 30 else 30))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 31 else 60) else (if i.val < 155 then 59 else 89)) else (if i.val < 158 then (if i.val < 157 then 61 else 30) else (if i.val < 159 then 63 else 66))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 57 else 14) else (if i.val < 163 then 59 else 16)) else (if i.val < 166 then (if i.val < 165 then 3 else 29) else (if i.val < 167 then 16 else 32))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 34 else 34) else (if i.val < 171 then 57 else 60)) else (if i.val < 174 then (if i.val < 173 then 17 else 15) else (if i.val < 175 then 57 else 57)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 33 else 29) else (if i.val < 179 then 60 else 30)) else (if i.val < 182 then (if i.val < 181 then 15 else 14) else (if i.val < 183 then 33 else 33))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 16 else 64) else (if i.val < 187 then 16 else 91)) else (if i.val < 190 then (if i.val < 189 then 30 else 29) else (if i.val < 191 then 57 else 92)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 30 else 60) else (if i.val < 195 then 62 else 16)) else (if i.val < 198 then (if i.val < 197 then 29 else 63) else (if i.val < 199 then 59 else 64))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 57 else 62) else (if i.val < 203 then 30 else 60)) else (if i.val < 206 then (if i.val < 205 then 34 else 60) else (if i.val < 207 then 29 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 34 else 34) else (if i.val < 211 then 91 else 60)) else (if i.val < 214 then (if i.val < 213 then 57 else 34) else (if i.val < 215 then 60 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 30) else (if i.val < 219 then 34 else 34)) else (if i.val < 222 then (if i.val < 221 then 4 else 29) else (if i.val < 223 then 4 else 14))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 59 else 88) else (if i.val < 227 then 14 else 88)) else (if i.val < 230 then (if i.val < 229 then 33 else 36) else (if i.val < 231 then 14 else 59))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 34) else (if i.val < 235 then 57 else 16)) else (if i.val < 238 then (if i.val < 237 then 34 else 66) else (if i.val < 239 then 57 else 30)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 36 else 4) else (if i.val < 243 then 34 else 57)) else (if i.val < 246 then (if i.val < 245 then 34 else 59) else (if i.val < 247 then 66 else 30))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 59 else 17) else (if i.val < 251 then 62 else 15)) else (if i.val < 254 then (if i.val < 253 then 57 else 14) else (if i.val < 255 then 30 else 62))))))))

theorem g32p_supplierForest_actual_049 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_049 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_049 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_105146
  · exact g32p_supplierForest_actual_105158
  · exact g32p_supplierForest_actual_105167
  · exact g32p_supplierForest_actual_105168
  · exact g32p_supplierForest_actual_105226
  · exact g32p_supplierForest_actual_105230
  · exact g32p_supplierForest_actual_105234
  · exact g32p_supplierForest_actual_105275
  · exact g32p_supplierForest_actual_105322
  · exact g32p_supplierForest_actual_105349
  · exact g32p_supplierForest_actual_105353
  · exact g32p_supplierForest_actual_105383
  · exact g32p_supplierForest_actual_105419
  · exact g32p_supplierForest_actual_105463
  · exact g32p_supplierForest_actual_105464
  · exact g32p_supplierForest_actual_105507
  · exact g32p_supplierForest_actual_105525
  · exact g32p_supplierForest_actual_105529
  · exact g32p_supplierForest_actual_105550
  · exact g32p_supplierForest_actual_105615
  · exact g32p_supplierForest_actual_105633
  · exact g32p_supplierForest_actual_105666
  · exact g32p_supplierForest_actual_105726
  · exact g32p_supplierForest_actual_105772
  · exact g32p_supplierForest_actual_105777
  · exact g32p_supplierForest_actual_105816
  · exact g32p_supplierForest_actual_105825
  · exact g32p_supplierForest_actual_105874
  · exact g32p_supplierForest_actual_105888
  · exact g32p_supplierForest_actual_105970
  · exact g32p_supplierForest_actual_106072
  · exact g32p_supplierForest_actual_106143
  · exact g32p_supplierForest_actual_106162
  · exact g32p_supplierForest_actual_106172
  · exact g32p_supplierForest_actual_106198
  · exact g32p_supplierForest_actual_106218
  · exact g32p_supplierForest_actual_106229
  · exact g32p_supplierForest_actual_106239
  · exact g32p_supplierForest_actual_106301
  · exact g32p_supplierForest_actual_106306
  · exact g32p_supplierForest_actual_106313
  · exact g32p_supplierForest_actual_106325
  · exact g32p_supplierForest_actual_106353
  · exact g32p_supplierForest_actual_106357
  · exact g32p_supplierForest_actual_106376
  · exact g32p_supplierForest_actual_106414
  · exact g32p_supplierForest_actual_106419
  · exact g32p_supplierForest_actual_106425
  · exact g32p_supplierForest_actual_106440
  · exact g32p_supplierForest_actual_106443
  · exact g32p_supplierForest_actual_106444
  · exact g32p_supplierForest_actual_106450
  · exact g32p_supplierForest_actual_106482
  · exact g32p_supplierForest_actual_106491
  · exact g32p_supplierForest_actual_106521
  · exact g32p_supplierForest_actual_106544
  · exact g32p_supplierForest_actual_106563
  · exact g32p_supplierForest_actual_106578
  · exact g32p_supplierForest_actual_106590
  · exact g32p_supplierForest_actual_106605
  · exact g32p_supplierForest_actual_106614
  · exact g32p_supplierForest_actual_106633
  · exact g32p_supplierForest_actual_106654
  · exact g32p_supplierForest_actual_106686
  · exact g32p_supplierForest_actual_106715
  · exact g32p_supplierForest_actual_106732
  · exact g32p_supplierForest_actual_106764
  · exact g32p_supplierForest_actual_106766
  · exact g32p_supplierForest_actual_106807
  · exact g32p_supplierForest_actual_106816
  · exact g32p_supplierForest_actual_106889
  · exact g32p_supplierForest_actual_106895
  · exact g32p_supplierForest_actual_106901
  · exact g32p_supplierForest_actual_106935
  · exact g32p_supplierForest_actual_106963
  · exact g32p_supplierForest_actual_107015
  · exact g32p_supplierForest_actual_107024
  · exact g32p_supplierForest_actual_107028
  · exact g32p_supplierForest_actual_107029
  · exact g32p_supplierForest_actual_107033
  · exact g32p_supplierForest_actual_107058
  · exact g32p_supplierForest_actual_107104
  · exact g32p_supplierForest_actual_107125
  · exact g32p_supplierForest_actual_107166
  · exact g32p_supplierForest_actual_107258
  · exact g32p_supplierForest_actual_107259
  · exact g32p_supplierForest_actual_107278
  · exact g32p_supplierForest_actual_107305
  · exact g32p_supplierForest_actual_107316
  · exact g32p_supplierForest_actual_107356
  · exact g32p_supplierForest_actual_107372
  · exact g32p_supplierForest_actual_107469
  · exact g32p_supplierForest_actual_107500
  · exact g32p_supplierForest_actual_107509
  · exact g32p_supplierForest_actual_107516
  · exact g32p_supplierForest_actual_107524
  · exact g32p_supplierForest_actual_107540
  · exact g32p_supplierForest_actual_107552
  · exact g32p_supplierForest_actual_107580
  · exact g32p_supplierForest_actual_107583
  · exact g32p_supplierForest_actual_107585
  · exact g32p_supplierForest_actual_107590
  · exact g32p_supplierForest_actual_107595
  · exact g32p_supplierForest_actual_107628
  · exact g32p_supplierForest_actual_107671
  · exact g32p_supplierForest_actual_107704
  · exact g32p_supplierForest_actual_107710
  · exact g32p_supplierForest_actual_107724
  · exact g32p_supplierForest_actual_107762
  · exact g32p_supplierForest_actual_107777
  · exact g32p_supplierForest_actual_107800
  · exact g32p_supplierForest_actual_107818
  · exact g32p_supplierForest_actual_107837
  · exact g32p_supplierForest_actual_107849
  · exact g32p_supplierForest_actual_107873
  · exact g32p_supplierForest_actual_107918
  · exact g32p_supplierForest_actual_107922
  · exact g32p_supplierForest_actual_107984
  · exact g32p_supplierForest_actual_107996
  · exact g32p_supplierForest_actual_108030
  · exact g32p_supplierForest_actual_108051
  · exact g32p_supplierForest_actual_108058
  · exact g32p_supplierForest_actual_108107
  · exact g32p_supplierForest_actual_108121
  · exact g32p_supplierForest_actual_108124
  · exact g32p_supplierForest_actual_108126
  · exact g32p_supplierForest_actual_108134
  · exact g32p_supplierForest_actual_108145
  · exact g32p_supplierForest_actual_108166
  · exact g32p_supplierForest_actual_108172
  · exact g32p_supplierForest_actual_108181
  · exact g32p_supplierForest_actual_108198
  · exact g32p_supplierForest_actual_108204
  · exact g32p_supplierForest_actual_108223
  · exact g32p_supplierForest_actual_108238
  · exact g32p_supplierForest_actual_108258
  · exact g32p_supplierForest_actual_108283
  · exact g32p_supplierForest_actual_108295
  · exact g32p_supplierForest_actual_108316
  · exact g32p_supplierForest_actual_108324
  · exact g32p_supplierForest_actual_108398
  · exact g32p_supplierForest_actual_108416
  · exact g32p_supplierForest_actual_108417
  · exact g32p_supplierForest_actual_108457
  · exact g32p_supplierForest_actual_108462
  · exact g32p_supplierForest_actual_108491
  · exact g32p_supplierForest_actual_108512
  · exact g32p_supplierForest_actual_108521
  · exact g32p_supplierForest_actual_108546
  · exact g32p_supplierForest_actual_108558
  · exact g32p_supplierForest_actual_108579
  · exact g32p_supplierForest_actual_108587
  · exact g32p_supplierForest_actual_108604
  · exact g32p_supplierForest_actual_108677
  · exact g32p_supplierForest_actual_108721
  · exact g32p_supplierForest_actual_108744
  · exact g32p_supplierForest_actual_108751
  · exact g32p_supplierForest_actual_108764
  · exact g32p_supplierForest_actual_108779
  · exact g32p_supplierForest_actual_108806
  · exact g32p_supplierForest_actual_108843
  · exact g32p_supplierForest_actual_108864
  · exact g32p_supplierForest_actual_108865
  · exact g32p_supplierForest_actual_108870
  · exact g32p_supplierForest_actual_108894
  · exact g32p_supplierForest_actual_109009
  · exact g32p_supplierForest_actual_109013
  · exact g32p_supplierForest_actual_109032
  · exact g32p_supplierForest_actual_109042
  · exact g32p_supplierForest_actual_109096
  · exact g32p_supplierForest_actual_109116
  · exact g32p_supplierForest_actual_109123
  · exact g32p_supplierForest_actual_109128
  · exact g32p_supplierForest_actual_109132
  · exact g32p_supplierForest_actual_109196
  · exact g32p_supplierForest_actual_109197
  · exact g32p_supplierForest_actual_109210
  · exact g32p_supplierForest_actual_109220
  · exact g32p_supplierForest_actual_109232
  · exact g32p_supplierForest_actual_109286
  · exact g32p_supplierForest_actual_109300
  · exact g32p_supplierForest_actual_109306
  · exact g32p_supplierForest_actual_109312
  · exact g32p_supplierForest_actual_109320
  · exact g32p_supplierForest_actual_109332
  · exact g32p_supplierForest_actual_109361
  · exact g32p_supplierForest_actual_109376
  · exact g32p_supplierForest_actual_109447
  · exact g32p_supplierForest_actual_109471
  · exact g32p_supplierForest_actual_109501
  · exact g32p_supplierForest_actual_109506
  · exact g32p_supplierForest_actual_109599
  · exact g32p_supplierForest_actual_109645
  · exact g32p_supplierForest_actual_109649
  · exact g32p_supplierForest_actual_109737
  · exact g32p_supplierForest_actual_109784
  · exact g32p_supplierForest_actual_109803
  · exact g32p_supplierForest_actual_109853
  · exact g32p_supplierForest_actual_109870
  · exact g32p_supplierForest_actual_109903
  · exact g32p_supplierForest_actual_109912
  · exact g32p_supplierForest_actual_109981
  · exact g32p_supplierForest_actual_109996
  · exact g32p_supplierForest_actual_110003
  · exact g32p_supplierForest_actual_110011
  · exact g32p_supplierForest_actual_110045
  · exact g32p_supplierForest_actual_110050
  · exact g32p_supplierForest_actual_110059
  · exact g32p_supplierForest_actual_110072
  · exact g32p_supplierForest_actual_110115
  · exact g32p_supplierForest_actual_110190
  · exact g32p_supplierForest_actual_110199
  · exact g32p_supplierForest_actual_110220
  · exact g32p_supplierForest_actual_110268
  · exact g32p_supplierForest_actual_110345
  · exact g32p_supplierForest_actual_110383
  · exact g32p_supplierForest_actual_110393
  · exact g32p_supplierForest_actual_110443
  · exact g32p_supplierForest_actual_110448
  · exact g32p_supplierForest_actual_110491
  · exact g32p_supplierForest_actual_110504
  · exact g32p_supplierForest_actual_110521
  · exact g32p_supplierForest_actual_110550
  · exact g32p_supplierForest_actual_110591
  · exact g32p_supplierForest_actual_110619
  · exact g32p_supplierForest_actual_110659
  · exact g32p_supplierForest_actual_110676
  · exact g32p_supplierForest_actual_110680
  · exact g32p_supplierForest_actual_110700
  · exact g32p_supplierForest_actual_110725
  · exact g32p_supplierForest_actual_110733
  · exact g32p_supplierForest_actual_110756
  · exact g32p_supplierForest_actual_110768
  · exact g32p_supplierForest_actual_110783
  · exact g32p_supplierForest_actual_110804
  · exact g32p_supplierForest_actual_110806
  · exact g32p_supplierForest_actual_110820
  · exact g32p_supplierForest_actual_110831
  · exact g32p_supplierForest_actual_110854
  · exact g32p_supplierForest_actual_110914
  · exact g32p_supplierForest_actual_110927
  · exact g32p_supplierForest_actual_110944
  · exact g32p_supplierForest_actual_110967
  · exact g32p_supplierForest_actual_110977
  · exact g32p_supplierForest_actual_111012
  · exact g32p_supplierForest_actual_111014
  · exact g32p_supplierForest_actual_111166
  · exact g32p_supplierForest_actual_111184
  · exact g32p_supplierForest_actual_111205
  · exact g32p_supplierForest_actual_111277
  · exact g32p_supplierForest_actual_111305
  · exact g32p_supplierForest_actual_111310
  · exact g32p_supplierForest_actual_111311
  · exact g32p_supplierForest_actual_111475
  · exact g32p_supplierForest_actual_111514
  · exact g32p_supplierForest_actual_111534

def g32p_supplierForest_nodes_050 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_111553 else g32p_supplierForest_node_111577) else (if i.val < 3 then g32p_supplierForest_node_111590 else g32p_supplierForest_node_111642)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_111652 else g32p_supplierForest_node_111657) else (if i.val < 7 then g32p_supplierForest_node_111700 else g32p_supplierForest_node_111712))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_111723 else g32p_supplierForest_node_111731) else (if i.val < 11 then g32p_supplierForest_node_111748 else g32p_supplierForest_node_111787)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_111908 else g32p_supplierForest_node_111925) else (if i.val < 15 then g32p_supplierForest_node_111941 else g32p_supplierForest_node_112035)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_112037 else g32p_supplierForest_node_112073) else (if i.val < 19 then g32p_supplierForest_node_112100 else g32p_supplierForest_node_112144)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_112293 else g32p_supplierForest_node_112315) else (if i.val < 23 then g32p_supplierForest_node_112355 else g32p_supplierForest_node_112387))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_112408 else g32p_supplierForest_node_112418) else (if i.val < 27 then g32p_supplierForest_node_112423 else g32p_supplierForest_node_112484)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_112503 else g32p_supplierForest_node_112507) else (if i.val < 31 then g32p_supplierForest_node_112515 else g32p_supplierForest_node_112525))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_112542 else g32p_supplierForest_node_112569) else (if i.val < 35 then g32p_supplierForest_node_112605 else g32p_supplierForest_node_112606)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_112715 else g32p_supplierForest_node_112763) else (if i.val < 39 then g32p_supplierForest_node_112769 else g32p_supplierForest_node_112774))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_112793 else g32p_supplierForest_node_112814) else (if i.val < 43 then g32p_supplierForest_node_112831 else g32p_supplierForest_node_112846)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_112868 else g32p_supplierForest_node_112874) else (if i.val < 47 then g32p_supplierForest_node_112894 else g32p_supplierForest_node_112910)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_112944 else g32p_supplierForest_node_112958) else (if i.val < 51 then g32p_supplierForest_node_112968 else g32p_supplierForest_node_112985)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_112995 else g32p_supplierForest_node_113012) else (if i.val < 55 then g32p_supplierForest_node_113030 else g32p_supplierForest_node_113047))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_113068 else g32p_supplierForest_node_113077) else (if i.val < 59 then g32p_supplierForest_node_113090 else g32p_supplierForest_node_113140)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_113162 else g32p_supplierForest_node_113186) else (if i.val < 63 then g32p_supplierForest_node_113230 else g32p_supplierForest_node_113340)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_113348 else g32p_supplierForest_node_113351) else (if i.val < 67 then g32p_supplierForest_node_113364 else g32p_supplierForest_node_113372)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_113402 else g32p_supplierForest_node_113432) else (if i.val < 71 then g32p_supplierForest_node_113451 else g32p_supplierForest_node_113463))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_113464 else g32p_supplierForest_node_113466) else (if i.val < 75 then g32p_supplierForest_node_113474 else g32p_supplierForest_node_113485)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_113490 else g32p_supplierForest_node_113518) else (if i.val < 79 then g32p_supplierForest_node_113539 else g32p_supplierForest_node_113552)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_113583 else g32p_supplierForest_node_113605) else (if i.val < 83 then g32p_supplierForest_node_113609 else g32p_supplierForest_node_113615)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_113616 else g32p_supplierForest_node_113631) else (if i.val < 87 then g32p_supplierForest_node_113641 else g32p_supplierForest_node_113655))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_113658 else g32p_supplierForest_node_113666) else (if i.val < 91 then g32p_supplierForest_node_113681 else g32p_supplierForest_node_113711)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_113719 else g32p_supplierForest_node_113794) else (if i.val < 95 then g32p_supplierForest_node_113804 else g32p_supplierForest_node_113809))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_113830 else g32p_supplierForest_node_113833) else (if i.val < 99 then g32p_supplierForest_node_113860 else g32p_supplierForest_node_113873)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_113900 else g32p_supplierForest_node_113927) else (if i.val < 103 then g32p_supplierForest_node_113930 else g32p_supplierForest_node_113934))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_113985 else g32p_supplierForest_node_113995) else (if i.val < 107 then g32p_supplierForest_node_114002 else g32p_supplierForest_node_114026)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_114028 else g32p_supplierForest_node_114041) else (if i.val < 111 then g32p_supplierForest_node_114044 else g32p_supplierForest_node_114048)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_114148 else g32p_supplierForest_node_114173) else (if i.val < 115 then g32p_supplierForest_node_114175 else g32p_supplierForest_node_114176)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_114199 else g32p_supplierForest_node_114216) else (if i.val < 119 then g32p_supplierForest_node_114259 else g32p_supplierForest_node_114284))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_114288 else g32p_supplierForest_node_114310) else (if i.val < 123 then g32p_supplierForest_node_114321 else g32p_supplierForest_node_114325)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_114351 else g32p_supplierForest_node_114352) else (if i.val < 127 then g32p_supplierForest_node_114424 else g32p_supplierForest_node_114472))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_114480 else g32p_supplierForest_node_114495) else (if i.val < 131 then g32p_supplierForest_node_114514 else g32p_supplierForest_node_114549)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_114557 else g32p_supplierForest_node_114564) else (if i.val < 135 then g32p_supplierForest_node_114599 else g32p_supplierForest_node_114673))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_114682 else g32p_supplierForest_node_114757) else (if i.val < 139 then g32p_supplierForest_node_114811 else g32p_supplierForest_node_114818)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_114851 else g32p_supplierForest_node_114852) else (if i.val < 143 then g32p_supplierForest_node_114972 else g32p_supplierForest_node_114974)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_114995 else g32p_supplierForest_node_115003) else (if i.val < 147 then g32p_supplierForest_node_115115 else g32p_supplierForest_node_115148)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_115171 else g32p_supplierForest_node_115180) else (if i.val < 151 then g32p_supplierForest_node_115247 else g32p_supplierForest_node_115327))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_115340 else g32p_supplierForest_node_115365) else (if i.val < 155 then g32p_supplierForest_node_115370 else g32p_supplierForest_node_115406)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_115449 else g32p_supplierForest_node_115454) else (if i.val < 159 then g32p_supplierForest_node_115456 else g32p_supplierForest_node_115462))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_115506 else g32p_supplierForest_node_115537) else (if i.val < 163 then g32p_supplierForest_node_115543 else g32p_supplierForest_node_115623)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_115625 else g32p_supplierForest_node_115648) else (if i.val < 167 then g32p_supplierForest_node_115654 else g32p_supplierForest_node_115672))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_115689 else g32p_supplierForest_node_115751) else (if i.val < 171 then g32p_supplierForest_node_115764 else g32p_supplierForest_node_115786)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_115845 else g32p_supplierForest_node_115874) else (if i.val < 175 then g32p_supplierForest_node_115911 else g32p_supplierForest_node_115937)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_116116 else g32p_supplierForest_node_116118) else (if i.val < 179 then g32p_supplierForest_node_116137 else g32p_supplierForest_node_116180)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_116219 else g32p_supplierForest_node_116249) else (if i.val < 183 then g32p_supplierForest_node_116299 else g32p_supplierForest_node_116300))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_116319 else g32p_supplierForest_node_116322) else (if i.val < 187 then g32p_supplierForest_node_116349 else g32p_supplierForest_node_116353)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_116451 else g32p_supplierForest_node_116452) else (if i.val < 191 then g32p_supplierForest_node_116453 else g32p_supplierForest_node_116464)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_116522 else g32p_supplierForest_node_116544) else (if i.val < 195 then g32p_supplierForest_node_116599 else g32p_supplierForest_node_116619)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_116639 else g32p_supplierForest_node_116675) else (if i.val < 199 then g32p_supplierForest_node_116790 else g32p_supplierForest_node_116799))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_116824 else g32p_supplierForest_node_116876) else (if i.val < 203 then g32p_supplierForest_node_116877 else g32p_supplierForest_node_116923)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_116989 else g32p_supplierForest_node_116990) else (if i.val < 207 then g32p_supplierForest_node_116997 else g32p_supplierForest_node_117001)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_117073 else g32p_supplierForest_node_117076) else (if i.val < 211 then g32p_supplierForest_node_117087 else g32p_supplierForest_node_117104)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_117117 else g32p_supplierForest_node_117128) else (if i.val < 215 then g32p_supplierForest_node_117140 else g32p_supplierForest_node_117145))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_117152 else g32p_supplierForest_node_117179) else (if i.val < 219 then g32p_supplierForest_node_117193 else g32p_supplierForest_node_117201)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_117208 else g32p_supplierForest_node_117225) else (if i.val < 223 then g32p_supplierForest_node_117230 else g32p_supplierForest_node_117237))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_117333 else g32p_supplierForest_node_117437) else (if i.val < 227 then g32p_supplierForest_node_117463 else g32p_supplierForest_node_117545)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_117575 else g32p_supplierForest_node_117578) else (if i.val < 231 then g32p_supplierForest_node_117668 else g32p_supplierForest_node_117686))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_117729 else g32p_supplierForest_node_117736) else (if i.val < 235 then g32p_supplierForest_node_117750 else g32p_supplierForest_node_117760)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_117765 else g32p_supplierForest_node_117768) else (if i.val < 239 then g32p_supplierForest_node_117801 else g32p_supplierForest_node_117803)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_117810 else g32p_supplierForest_node_117833) else (if i.val < 243 then g32p_supplierForest_node_117930 else g32p_supplierForest_node_117971)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_117975 else g32p_supplierForest_node_118001) else (if i.val < 247 then g32p_supplierForest_node_118008 else g32p_supplierForest_node_118047))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_118067 else g32p_supplierForest_node_118078) else (if i.val < 251 then g32p_supplierForest_node_118113 else g32p_supplierForest_node_118145)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_118202 else g32p_supplierForest_node_118257) else (if i.val < 255 then g32p_supplierForest_node_118271 else g32p_supplierForest_node_118311))))))))

def g32p_supplierForest_classes_050 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 66 else 57) else (if i.val < 3 then 66 else 62)) else (if i.val < 6 then (if i.val < 5 then 57 else 66) else (if i.val < 7 then 66 else 66))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 29 else 59) else (if i.val < 11 then 33 else 57)) else (if i.val < 14 then (if i.val < 13 then 29 else 29) else (if i.val < 15 then 63 else 60)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 59 else 63) else (if i.val < 19 then 34 else 57)) else (if i.val < 22 then (if i.val < 21 then 36 else 57) else (if i.val < 23 then 34 else 29))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 30 else 16) else (if i.val < 27 then 57 else 34)) else (if i.val < 30 then (if i.val < 29 then 30 else 90) else (if i.val < 31 then 17 else 16))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 29 else 17) else (if i.val < 35 then 58 else 92)) else (if i.val < 38 then (if i.val < 37 then 29 else 35) else (if i.val < 39 then 30 else 29))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 60 else 30) else (if i.val < 43 then 57 else 30)) else (if i.val < 46 then (if i.val < 45 then 30 else 57) else (if i.val < 47 then 30 else 58)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 32 else 62) else (if i.val < 51 then 58 else 35)) else (if i.val < 54 then (if i.val < 53 then 60 else 60) else (if i.val < 55 then 16 else 62))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 30 else 36) else (if i.val < 59 then 61 else 57)) else (if i.val < 62 then (if i.val < 61 then 33 else 30) else (if i.val < 63 then 30 else 65)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 66 else 58) else (if i.val < 67 then 29 else 15)) else (if i.val < 70 then (if i.val < 69 then 30 else 60) else (if i.val < 71 then 59 else 57))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 64 else 64) else (if i.val < 75 then 16 else 57)) else (if i.val < 78 then (if i.val < 77 then 4 else 16) else (if i.val < 79 then 30 else 36)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 15 else 57) else (if i.val < 83 then 60 else 66)) else (if i.val < 86 then (if i.val < 85 then 66 else 57) else (if i.val < 87 then 63 else 30))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 59 else 65) else (if i.val < 91 then 30 else 35)) else (if i.val < 94 then (if i.val < 93 then 33 else 30) else (if i.val < 95 then 57 else 29))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 29 else 60) else (if i.val < 99 then 62 else 59)) else (if i.val < 102 then (if i.val < 101 then 30 else 58) else (if i.val < 103 then 58 else 60))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 59 else 17) else (if i.val < 107 then 57 else 30)) else (if i.val < 110 then (if i.val < 109 then 65 else 34) else (if i.val < 111 then 66 else 60)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 60 else 17) else (if i.val < 115 then 30 else 16)) else (if i.val < 118 then (if i.val < 117 then 57 else 57) else (if i.val < 119 then 57 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 59 else 29) else (if i.val < 123 then 34 else 36)) else (if i.val < 126 then (if i.val < 125 then 60 else 61) else (if i.val < 127 then 30 else 57))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 57 else 30) else (if i.val < 131 then 31 else 34)) else (if i.val < 134 then (if i.val < 133 then 57 else 57) else (if i.val < 135 then 16 else 61))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 92 else 57) else (if i.val < 139 then 59 else 59)) else (if i.val < 142 then (if i.val < 141 then 36 else 34) else (if i.val < 143 then 57 else 36)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 16 else 57) else (if i.val < 147 then 60 else 60)) else (if i.val < 150 then (if i.val < 149 then 63 else 62) else (if i.val < 151 then 61 else 59))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 59 else 57) else (if i.val < 155 then 57 else 57)) else (if i.val < 158 then (if i.val < 157 then 58 else 29) else (if i.val < 159 then 29 else 35))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 29 else 30) else (if i.val < 163 then 33 else 14)) else (if i.val < 166 then (if i.val < 165 then 16 else 57) else (if i.val < 167 then 29 else 30))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 66 else 30) else (if i.val < 171 then 4 else 60)) else (if i.val < 174 then (if i.val < 173 then 60 else 33) else (if i.val < 175 then 34 else 60)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 29 else 59) else (if i.val < 179 then 58 else 60)) else (if i.val < 182 then (if i.val < 181 then 58 else 61) else (if i.val < 183 then 29 else 36))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 60 else 33) else (if i.val < 187 then 59 else 61)) else (if i.val < 190 then (if i.val < 189 then 17 else 29) else (if i.val < 191 then 60 else 58)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 66 else 62) else (if i.val < 195 then 57 else 60)) else (if i.val < 198 then (if i.val < 197 then 29 else 30) else (if i.val < 199 then 57 else 36))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 64 else 62) else (if i.val < 203 then 93 else 34)) else (if i.val < 206 then (if i.val < 205 then 29 else 29) else (if i.val < 207 then 34 else 29)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 58 else 60) else (if i.val < 211 then 57 else 35)) else (if i.val < 214 then (if i.val < 213 then 60 else 35) else (if i.val < 215 then 66 else 92))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 66 else 35) else (if i.val < 219 then 60 else 57)) else (if i.val < 222 then (if i.val < 221 then 29 else 66) else (if i.val < 223 then 57 else 59))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 60 else 17) else (if i.val < 227 then 60 else 59)) else (if i.val < 230 then (if i.val < 229 then 30 else 57) else (if i.val < 231 then 33 else 61))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 62) else (if i.val < 235 then 35 else 29)) else (if i.val < 238 then (if i.val < 237 then 33 else 35) else (if i.val < 239 then 30 else 33)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 92 else 66) else (if i.val < 243 then 90 else 60)) else (if i.val < 246 then (if i.val < 245 then 33 else 30) else (if i.val < 247 then 66 else 66))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 59 else 89) else (if i.val < 251 then 59 else 29)) else (if i.val < 254 then (if i.val < 253 then 60 else 30) else (if i.val < 255 then 58 else 30))))))))

theorem g32p_supplierForest_actual_050 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_050 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_050 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_111553
  · exact g32p_supplierForest_actual_111577
  · exact g32p_supplierForest_actual_111590
  · exact g32p_supplierForest_actual_111642
  · exact g32p_supplierForest_actual_111652
  · exact g32p_supplierForest_actual_111657
  · exact g32p_supplierForest_actual_111700
  · exact g32p_supplierForest_actual_111712
  · exact g32p_supplierForest_actual_111723
  · exact g32p_supplierForest_actual_111731
  · exact g32p_supplierForest_actual_111748
  · exact g32p_supplierForest_actual_111787
  · exact g32p_supplierForest_actual_111908
  · exact g32p_supplierForest_actual_111925
  · exact g32p_supplierForest_actual_111941
  · exact g32p_supplierForest_actual_112035
  · exact g32p_supplierForest_actual_112037
  · exact g32p_supplierForest_actual_112073
  · exact g32p_supplierForest_actual_112100
  · exact g32p_supplierForest_actual_112144
  · exact g32p_supplierForest_actual_112293
  · exact g32p_supplierForest_actual_112315
  · exact g32p_supplierForest_actual_112355
  · exact g32p_supplierForest_actual_112387
  · exact g32p_supplierForest_actual_112408
  · exact g32p_supplierForest_actual_112418
  · exact g32p_supplierForest_actual_112423
  · exact g32p_supplierForest_actual_112484
  · exact g32p_supplierForest_actual_112503
  · exact g32p_supplierForest_actual_112507
  · exact g32p_supplierForest_actual_112515
  · exact g32p_supplierForest_actual_112525
  · exact g32p_supplierForest_actual_112542
  · exact g32p_supplierForest_actual_112569
  · exact g32p_supplierForest_actual_112605
  · exact g32p_supplierForest_actual_112606
  · exact g32p_supplierForest_actual_112715
  · exact g32p_supplierForest_actual_112763
  · exact g32p_supplierForest_actual_112769
  · exact g32p_supplierForest_actual_112774
  · exact g32p_supplierForest_actual_112793
  · exact g32p_supplierForest_actual_112814
  · exact g32p_supplierForest_actual_112831
  · exact g32p_supplierForest_actual_112846
  · exact g32p_supplierForest_actual_112868
  · exact g32p_supplierForest_actual_112874
  · exact g32p_supplierForest_actual_112894
  · exact g32p_supplierForest_actual_112910
  · exact g32p_supplierForest_actual_112944
  · exact g32p_supplierForest_actual_112958
  · exact g32p_supplierForest_actual_112968
  · exact g32p_supplierForest_actual_112985
  · exact g32p_supplierForest_actual_112995
  · exact g32p_supplierForest_actual_113012
  · exact g32p_supplierForest_actual_113030
  · exact g32p_supplierForest_actual_113047
  · exact g32p_supplierForest_actual_113068
  · exact g32p_supplierForest_actual_113077
  · exact g32p_supplierForest_actual_113090
  · exact g32p_supplierForest_actual_113140
  · exact g32p_supplierForest_actual_113162
  · exact g32p_supplierForest_actual_113186
  · exact g32p_supplierForest_actual_113230
  · exact g32p_supplierForest_actual_113340
  · exact g32p_supplierForest_actual_113348
  · exact g32p_supplierForest_actual_113351
  · exact g32p_supplierForest_actual_113364
  · exact g32p_supplierForest_actual_113372
  · exact g32p_supplierForest_actual_113402
  · exact g32p_supplierForest_actual_113432
  · exact g32p_supplierForest_actual_113451
  · exact g32p_supplierForest_actual_113463
  · exact g32p_supplierForest_actual_113464
  · exact g32p_supplierForest_actual_113466
  · exact g32p_supplierForest_actual_113474
  · exact g32p_supplierForest_actual_113485
  · exact g32p_supplierForest_actual_113490
  · exact g32p_supplierForest_actual_113518
  · exact g32p_supplierForest_actual_113539
  · exact g32p_supplierForest_actual_113552
  · exact g32p_supplierForest_actual_113583
  · exact g32p_supplierForest_actual_113605
  · exact g32p_supplierForest_actual_113609
  · exact g32p_supplierForest_actual_113615
  · exact g32p_supplierForest_actual_113616
  · exact g32p_supplierForest_actual_113631
  · exact g32p_supplierForest_actual_113641
  · exact g32p_supplierForest_actual_113655
  · exact g32p_supplierForest_actual_113658
  · exact g32p_supplierForest_actual_113666
  · exact g32p_supplierForest_actual_113681
  · exact g32p_supplierForest_actual_113711
  · exact g32p_supplierForest_actual_113719
  · exact g32p_supplierForest_actual_113794
  · exact g32p_supplierForest_actual_113804
  · exact g32p_supplierForest_actual_113809
  · exact g32p_supplierForest_actual_113830
  · exact g32p_supplierForest_actual_113833
  · exact g32p_supplierForest_actual_113860
  · exact g32p_supplierForest_actual_113873
  · exact g32p_supplierForest_actual_113900
  · exact g32p_supplierForest_actual_113927
  · exact g32p_supplierForest_actual_113930
  · exact g32p_supplierForest_actual_113934
  · exact g32p_supplierForest_actual_113985
  · exact g32p_supplierForest_actual_113995
  · exact g32p_supplierForest_actual_114002
  · exact g32p_supplierForest_actual_114026
  · exact g32p_supplierForest_actual_114028
  · exact g32p_supplierForest_actual_114041
  · exact g32p_supplierForest_actual_114044
  · exact g32p_supplierForest_actual_114048
  · exact g32p_supplierForest_actual_114148
  · exact g32p_supplierForest_actual_114173
  · exact g32p_supplierForest_actual_114175
  · exact g32p_supplierForest_actual_114176
  · exact g32p_supplierForest_actual_114199
  · exact g32p_supplierForest_actual_114216
  · exact g32p_supplierForest_actual_114259
  · exact g32p_supplierForest_actual_114284
  · exact g32p_supplierForest_actual_114288
  · exact g32p_supplierForest_actual_114310
  · exact g32p_supplierForest_actual_114321
  · exact g32p_supplierForest_actual_114325
  · exact g32p_supplierForest_actual_114351
  · exact g32p_supplierForest_actual_114352
  · exact g32p_supplierForest_actual_114424
  · exact g32p_supplierForest_actual_114472
  · exact g32p_supplierForest_actual_114480
  · exact g32p_supplierForest_actual_114495
  · exact g32p_supplierForest_actual_114514
  · exact g32p_supplierForest_actual_114549
  · exact g32p_supplierForest_actual_114557
  · exact g32p_supplierForest_actual_114564
  · exact g32p_supplierForest_actual_114599
  · exact g32p_supplierForest_actual_114673
  · exact g32p_supplierForest_actual_114682
  · exact g32p_supplierForest_actual_114757
  · exact g32p_supplierForest_actual_114811
  · exact g32p_supplierForest_actual_114818
  · exact g32p_supplierForest_actual_114851
  · exact g32p_supplierForest_actual_114852
  · exact g32p_supplierForest_actual_114972
  · exact g32p_supplierForest_actual_114974
  · exact g32p_supplierForest_actual_114995
  · exact g32p_supplierForest_actual_115003
  · exact g32p_supplierForest_actual_115115
  · exact g32p_supplierForest_actual_115148
  · exact g32p_supplierForest_actual_115171
  · exact g32p_supplierForest_actual_115180
  · exact g32p_supplierForest_actual_115247
  · exact g32p_supplierForest_actual_115327
  · exact g32p_supplierForest_actual_115340
  · exact g32p_supplierForest_actual_115365
  · exact g32p_supplierForest_actual_115370
  · exact g32p_supplierForest_actual_115406
  · exact g32p_supplierForest_actual_115449
  · exact g32p_supplierForest_actual_115454
  · exact g32p_supplierForest_actual_115456
  · exact g32p_supplierForest_actual_115462
  · exact g32p_supplierForest_actual_115506
  · exact g32p_supplierForest_actual_115537
  · exact g32p_supplierForest_actual_115543
  · exact g32p_supplierForest_actual_115623
  · exact g32p_supplierForest_actual_115625
  · exact g32p_supplierForest_actual_115648
  · exact g32p_supplierForest_actual_115654
  · exact g32p_supplierForest_actual_115672
  · exact g32p_supplierForest_actual_115689
  · exact g32p_supplierForest_actual_115751
  · exact g32p_supplierForest_actual_115764
  · exact g32p_supplierForest_actual_115786
  · exact g32p_supplierForest_actual_115845
  · exact g32p_supplierForest_actual_115874
  · exact g32p_supplierForest_actual_115911
  · exact g32p_supplierForest_actual_115937
  · exact g32p_supplierForest_actual_116116
  · exact g32p_supplierForest_actual_116118
  · exact g32p_supplierForest_actual_116137
  · exact g32p_supplierForest_actual_116180
  · exact g32p_supplierForest_actual_116219
  · exact g32p_supplierForest_actual_116249
  · exact g32p_supplierForest_actual_116299
  · exact g32p_supplierForest_actual_116300
  · exact g32p_supplierForest_actual_116319
  · exact g32p_supplierForest_actual_116322
  · exact g32p_supplierForest_actual_116349
  · exact g32p_supplierForest_actual_116353
  · exact g32p_supplierForest_actual_116451
  · exact g32p_supplierForest_actual_116452
  · exact g32p_supplierForest_actual_116453
  · exact g32p_supplierForest_actual_116464
  · exact g32p_supplierForest_actual_116522
  · exact g32p_supplierForest_actual_116544
  · exact g32p_supplierForest_actual_116599
  · exact g32p_supplierForest_actual_116619
  · exact g32p_supplierForest_actual_116639
  · exact g32p_supplierForest_actual_116675
  · exact g32p_supplierForest_actual_116790
  · exact g32p_supplierForest_actual_116799
  · exact g32p_supplierForest_actual_116824
  · exact g32p_supplierForest_actual_116876
  · exact g32p_supplierForest_actual_116877
  · exact g32p_supplierForest_actual_116923
  · exact g32p_supplierForest_actual_116989
  · exact g32p_supplierForest_actual_116990
  · exact g32p_supplierForest_actual_116997
  · exact g32p_supplierForest_actual_117001
  · exact g32p_supplierForest_actual_117073
  · exact g32p_supplierForest_actual_117076
  · exact g32p_supplierForest_actual_117087
  · exact g32p_supplierForest_actual_117104
  · exact g32p_supplierForest_actual_117117
  · exact g32p_supplierForest_actual_117128
  · exact g32p_supplierForest_actual_117140
  · exact g32p_supplierForest_actual_117145
  · exact g32p_supplierForest_actual_117152
  · exact g32p_supplierForest_actual_117179
  · exact g32p_supplierForest_actual_117193
  · exact g32p_supplierForest_actual_117201
  · exact g32p_supplierForest_actual_117208
  · exact g32p_supplierForest_actual_117225
  · exact g32p_supplierForest_actual_117230
  · exact g32p_supplierForest_actual_117237
  · exact g32p_supplierForest_actual_117333
  · exact g32p_supplierForest_actual_117437
  · exact g32p_supplierForest_actual_117463
  · exact g32p_supplierForest_actual_117545
  · exact g32p_supplierForest_actual_117575
  · exact g32p_supplierForest_actual_117578
  · exact g32p_supplierForest_actual_117668
  · exact g32p_supplierForest_actual_117686
  · exact g32p_supplierForest_actual_117729
  · exact g32p_supplierForest_actual_117736
  · exact g32p_supplierForest_actual_117750
  · exact g32p_supplierForest_actual_117760
  · exact g32p_supplierForest_actual_117765
  · exact g32p_supplierForest_actual_117768
  · exact g32p_supplierForest_actual_117801
  · exact g32p_supplierForest_actual_117803
  · exact g32p_supplierForest_actual_117810
  · exact g32p_supplierForest_actual_117833
  · exact g32p_supplierForest_actual_117930
  · exact g32p_supplierForest_actual_117971
  · exact g32p_supplierForest_actual_117975
  · exact g32p_supplierForest_actual_118001
  · exact g32p_supplierForest_actual_118008
  · exact g32p_supplierForest_actual_118047
  · exact g32p_supplierForest_actual_118067
  · exact g32p_supplierForest_actual_118078
  · exact g32p_supplierForest_actual_118113
  · exact g32p_supplierForest_actual_118145
  · exact g32p_supplierForest_actual_118202
  · exact g32p_supplierForest_actual_118257
  · exact g32p_supplierForest_actual_118271
  · exact g32p_supplierForest_actual_118311

def g32p_supplierForest_nodes_051 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_118365 else g32p_supplierForest_node_118391) else (if i.val < 3 then g32p_supplierForest_node_118398 else g32p_supplierForest_node_118412)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_118465 else g32p_supplierForest_node_118469) else (if i.val < 7 then g32p_supplierForest_node_118481 else g32p_supplierForest_node_118491))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_118501 else g32p_supplierForest_node_118527) else (if i.val < 11 then g32p_supplierForest_node_118529 else g32p_supplierForest_node_118548)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_118570 else g32p_supplierForest_node_118579) else (if i.val < 15 then g32p_supplierForest_node_118644 else g32p_supplierForest_node_118654)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_118676 else g32p_supplierForest_node_118682) else (if i.val < 19 then g32p_supplierForest_node_118702 else g32p_supplierForest_node_118708)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_118731 else g32p_supplierForest_node_118848) else (if i.val < 23 then g32p_supplierForest_node_118862 else g32p_supplierForest_node_118872))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_118880 else g32p_supplierForest_node_118922) else (if i.val < 27 then g32p_supplierForest_node_119000 else g32p_supplierForest_node_119019)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_119088 else g32p_supplierForest_node_119089) else (if i.val < 31 then g32p_supplierForest_node_119167 else g32p_supplierForest_node_119261))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_119303 else g32p_supplierForest_node_119321) else (if i.val < 35 then g32p_supplierForest_node_119327 else g32p_supplierForest_node_119369)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_119386 else g32p_supplierForest_node_119390) else (if i.val < 39 then g32p_supplierForest_node_119404 else g32p_supplierForest_node_119426))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_119429 else g32p_supplierForest_node_119430) else (if i.val < 43 then g32p_supplierForest_node_119438 else g32p_supplierForest_node_119440)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_119517 else g32p_supplierForest_node_119571) else (if i.val < 47 then g32p_supplierForest_node_119593 else g32p_supplierForest_node_119602)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_119607 else g32p_supplierForest_node_119695) else (if i.val < 51 then g32p_supplierForest_node_119731 else g32p_supplierForest_node_119759)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_119828 else g32p_supplierForest_node_119884) else (if i.val < 55 then g32p_supplierForest_node_119909 else g32p_supplierForest_node_119912))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_119960 else g32p_supplierForest_node_119970) else (if i.val < 59 then g32p_supplierForest_node_119972 else g32p_supplierForest_node_120040)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_120041 else g32p_supplierForest_node_120057) else (if i.val < 63 then g32p_supplierForest_node_120062 else g32p_supplierForest_node_120129)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_120139 else g32p_supplierForest_node_120158) else (if i.val < 67 then g32p_supplierForest_node_120182 else g32p_supplierForest_node_120219)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_120220 else g32p_supplierForest_node_120222) else (if i.val < 71 then g32p_supplierForest_node_120260 else g32p_supplierForest_node_120279))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_120309 else g32p_supplierForest_node_120313) else (if i.val < 75 then g32p_supplierForest_node_120314 else g32p_supplierForest_node_120354)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_120375 else g32p_supplierForest_node_120389) else (if i.val < 79 then g32p_supplierForest_node_120465 else g32p_supplierForest_node_120469)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_120481 else g32p_supplierForest_node_120486) else (if i.val < 83 then g32p_supplierForest_node_120548 else g32p_supplierForest_node_120603)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_120751 else g32p_supplierForest_node_120752) else (if i.val < 87 then g32p_supplierForest_node_120755 else g32p_supplierForest_node_120779))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_120803 else g32p_supplierForest_node_120854) else (if i.val < 91 then g32p_supplierForest_node_120876 else g32p_supplierForest_node_120893)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_120906 else g32p_supplierForest_node_120933) else (if i.val < 95 then g32p_supplierForest_node_120942 else g32p_supplierForest_node_120951))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_121001 else g32p_supplierForest_node_121120) else (if i.val < 99 then g32p_supplierForest_node_121180 else g32p_supplierForest_node_121191)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_121230 else g32p_supplierForest_node_121249) else (if i.val < 103 then g32p_supplierForest_node_121260 else g32p_supplierForest_node_121261))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_121369 else g32p_supplierForest_node_121410) else (if i.val < 107 then g32p_supplierForest_node_121415 else g32p_supplierForest_node_121424)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_121434 else g32p_supplierForest_node_121443) else (if i.val < 111 then g32p_supplierForest_node_121522 else g32p_supplierForest_node_121567)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_121642 else g32p_supplierForest_node_121697) else (if i.val < 115 then g32p_supplierForest_node_121712 else g32p_supplierForest_node_121733)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_121793 else g32p_supplierForest_node_121833) else (if i.val < 119 then g32p_supplierForest_node_121854 else g32p_supplierForest_node_121866))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_121880 else g32p_supplierForest_node_121899) else (if i.val < 123 then g32p_supplierForest_node_121935 else g32p_supplierForest_node_121999)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_122023 else g32p_supplierForest_node_122025) else (if i.val < 127 then g32p_supplierForest_node_122044 else g32p_supplierForest_node_122047))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_122083 else g32p_supplierForest_node_122088) else (if i.val < 131 then g32p_supplierForest_node_122111 else g32p_supplierForest_node_122124)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_122167 else g32p_supplierForest_node_122168) else (if i.val < 135 then g32p_supplierForest_node_122174 else g32p_supplierForest_node_122188))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_122190 else g32p_supplierForest_node_122240) else (if i.val < 139 then g32p_supplierForest_node_122244 else g32p_supplierForest_node_122268)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_122270 else g32p_supplierForest_node_122286) else (if i.val < 143 then g32p_supplierForest_node_122316 else g32p_supplierForest_node_122323)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_122334 else g32p_supplierForest_node_122349) else (if i.val < 147 then g32p_supplierForest_node_122365 else g32p_supplierForest_node_122366)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_122367 else g32p_supplierForest_node_122383) else (if i.val < 151 then g32p_supplierForest_node_122385 else g32p_supplierForest_node_122409))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_122422 else g32p_supplierForest_node_122442) else (if i.val < 155 then g32p_supplierForest_node_122480 else g32p_supplierForest_node_122505)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_122532 else g32p_supplierForest_node_122556) else (if i.val < 159 then g32p_supplierForest_node_122570 else g32p_supplierForest_node_122626))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_122637 else g32p_supplierForest_node_122648) else (if i.val < 163 then g32p_supplierForest_node_122665 else g32p_supplierForest_node_122670)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_122689 else g32p_supplierForest_node_122708) else (if i.val < 167 then g32p_supplierForest_node_122715 else g32p_supplierForest_node_122718))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_122728 else g32p_supplierForest_node_122761) else (if i.val < 171 then g32p_supplierForest_node_122764 else g32p_supplierForest_node_122868)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_122896 else g32p_supplierForest_node_122904) else (if i.val < 175 then g32p_supplierForest_node_122927 else g32p_supplierForest_node_122951)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_122965 else g32p_supplierForest_node_122974) else (if i.val < 179 then g32p_supplierForest_node_123066 else g32p_supplierForest_node_123115)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_123125 else g32p_supplierForest_node_123143) else (if i.val < 183 then g32p_supplierForest_node_123175 else g32p_supplierForest_node_123189))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_123233 else g32p_supplierForest_node_123288) else (if i.val < 187 then g32p_supplierForest_node_123333 else g32p_supplierForest_node_123355)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_123356 else g32p_supplierForest_node_123387) else (if i.val < 191 then g32p_supplierForest_node_123403 else g32p_supplierForest_node_123409)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_123449 else g32p_supplierForest_node_123563) else (if i.val < 195 then g32p_supplierForest_node_123568 else g32p_supplierForest_node_123570)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_123582 else g32p_supplierForest_node_123598) else (if i.val < 199 then g32p_supplierForest_node_123601 else g32p_supplierForest_node_123629))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_123642 else g32p_supplierForest_node_123654) else (if i.val < 203 then g32p_supplierForest_node_123672 else g32p_supplierForest_node_123680)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_123686 else g32p_supplierForest_node_123728) else (if i.val < 207 then g32p_supplierForest_node_123751 else g32p_supplierForest_node_123797)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_123820 else g32p_supplierForest_node_123834) else (if i.val < 211 then g32p_supplierForest_node_123847 else g32p_supplierForest_node_123870)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_123922 else g32p_supplierForest_node_123929) else (if i.val < 215 then g32p_supplierForest_node_123977 else g32p_supplierForest_node_123996))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_124014 else g32p_supplierForest_node_124074) else (if i.val < 219 then g32p_supplierForest_node_124082 else g32p_supplierForest_node_124087)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_124106 else g32p_supplierForest_node_124110) else (if i.val < 223 then g32p_supplierForest_node_124114 else g32p_supplierForest_node_124209))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_124221 else g32p_supplierForest_node_124263) else (if i.val < 227 then g32p_supplierForest_node_124294 else g32p_supplierForest_node_124295)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_124322 else g32p_supplierForest_node_124351) else (if i.val < 231 then g32p_supplierForest_node_124354 else g32p_supplierForest_node_124374))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_124388 else g32p_supplierForest_node_124405) else (if i.val < 235 then g32p_supplierForest_node_124421 else g32p_supplierForest_node_124425)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_124431 else g32p_supplierForest_node_124435) else (if i.val < 239 then g32p_supplierForest_node_124444 else g32p_supplierForest_node_124469)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_124513 else g32p_supplierForest_node_124538) else (if i.val < 243 then g32p_supplierForest_node_124671 else g32p_supplierForest_node_124751)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_124832 else g32p_supplierForest_node_124890) else (if i.val < 247 then g32p_supplierForest_node_124892 else g32p_supplierForest_node_124923))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_124944 else g32p_supplierForest_node_124951) else (if i.val < 251 then g32p_supplierForest_node_124952 else g32p_supplierForest_node_124953)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_124960 else g32p_supplierForest_node_124983) else (if i.val < 255 then g32p_supplierForest_node_124995 else g32p_supplierForest_node_124997))))))))

def g32p_supplierForest_classes_051 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 62 else 36) else (if i.val < 3 then 60 else 61)) else (if i.val < 6 then (if i.val < 5 then 60 else 92) else (if i.val < 7 then 66 else 62))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 66 else 30) else (if i.val < 11 then 66 else 36)) else (if i.val < 14 then (if i.val < 13 then 35 else 57) else (if i.val < 15 then 59 else 34)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 36 else 30) else (if i.val < 19 then 29 else 63)) else (if i.val < 22 then (if i.val < 21 then 57 else 30) else (if i.val < 23 then 33 else 62))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 91 else 61) else (if i.val < 27 then 65 else 62)) else (if i.val < 30 then (if i.val < 29 then 65 else 15) else (if i.val < 31 then 60 else 60))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 64 else 61) else (if i.val < 35 then 61 else 30)) else (if i.val < 38 then (if i.val < 37 then 34 else 66) else (if i.val < 39 then 29 else 62))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 29 else 57) else (if i.val < 43 then 66 else 66)) else (if i.val < 46 then (if i.val < 45 then 34 else 34) else (if i.val < 47 then 66 else 62)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 30 else 29) else (if i.val < 51 then 33 else 30)) else (if i.val < 54 then (if i.val < 53 then 29 else 66) else (if i.val < 55 then 66 else 60))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 90 else 91) else (if i.val < 59 then 90 else 65)) else (if i.val < 62 then (if i.val < 61 then 57 else 62) else (if i.val < 63 then 62 else 65)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 36 else 57) else (if i.val < 67 then 61 else 30)) else (if i.val < 70 then (if i.val < 69 then 57 else 91) else (if i.val < 71 then 66 else 60))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 60 else 58) else (if i.val < 75 then 33 else 29)) else (if i.val < 78 then (if i.val < 77 then 60 else 35) else (if i.val < 79 then 91 else 66)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 66 else 60) else (if i.val < 83 then 60 else 59)) else (if i.val < 86 then (if i.val < 85 then 60 else 62) else (if i.val < 87 then 35 else 30))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 66 else 62) else (if i.val < 91 then 66 else 34)) else (if i.val < 94 then (if i.val < 93 then 61 else 66) else (if i.val < 95 then 30 else 63))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 34 else 58) else (if i.val < 99 then 35 else 59)) else (if i.val < 102 then (if i.val < 101 then 60 else 91) else (if i.val < 103 then 57 else 92))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 30 else 66) else (if i.val < 107 then 60 else 30)) else (if i.val < 110 then (if i.val < 109 then 58 else 66) else (if i.val < 111 then 29 else 33)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 60 else 60) else (if i.val < 115 then 34 else 30)) else (if i.val < 118 then (if i.val < 117 then 66 else 61) else (if i.val < 119 then 63 else 58))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 61 else 60) else (if i.val < 123 then 57 else 60)) else (if i.val < 126 then (if i.val < 125 then 30 else 66) else (if i.val < 127 then 57 else 61))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 30 else 33) else (if i.val < 131 then 92 else 60)) else (if i.val < 134 then (if i.val < 133 then 30 else 29) else (if i.val < 135 then 57 else 15))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 62 else 58) else (if i.val < 139 then 61 else 91)) else (if i.val < 142 then (if i.val < 141 then 92 else 90) else (if i.val < 143 then 36 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 66 else 90) else (if i.val < 147 then 62 else 60)) else (if i.val < 150 then (if i.val < 149 then 14 else 29) else (if i.val < 151 then 29 else 34))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 66 else 35) else (if i.val < 155 then 60 else 30)) else (if i.val < 158 then (if i.val < 157 then 57 else 90) else (if i.val < 159 then 34 else 60))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 35 else 59) else (if i.val < 163 then 60 else 66)) else (if i.val < 166 then (if i.val < 165 then 57 else 34) else (if i.val < 167 then 59 else 29))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 29 else 59) else (if i.val < 171 then 60 else 35)) else (if i.val < 174 then (if i.val < 173 then 61 else 90) else (if i.val < 175 then 92 else 59)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 57 else 60) else (if i.val < 179 then 30 else 62)) else (if i.val < 182 then (if i.val < 181 then 57 else 30) else (if i.val < 183 then 60 else 90))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 61) else (if i.val < 187 then 61 else 35)) else (if i.val < 190 then (if i.val < 189 then 61 else 89) else (if i.val < 191 then 89 else 60)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 34 else 66) else (if i.val < 195 then 57 else 34)) else (if i.val < 198 then (if i.val < 197 then 35 else 92) else (if i.val < 199 then 91 else 34))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 65 else 34) else (if i.val < 203 then 34 else 66)) else (if i.val < 206 then (if i.val < 205 then 66 else 60) else (if i.val < 207 then 87 else 91)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 35 else 57) else (if i.val < 211 then 30 else 58)) else (if i.val < 214 then (if i.val < 213 then 59 else 35) else (if i.val < 215 then 57 else 92))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 61 else 35) else (if i.val < 219 then 30 else 29)) else (if i.val < 222 then (if i.val < 221 then 62 else 30) else (if i.val < 223 then 34 else 90))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 87 else 35) else (if i.val < 227 then 59 else 91)) else (if i.val < 230 then (if i.val < 229 then 34 else 91) else (if i.val < 231 then 60 else 35))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 58 else 35) else (if i.val < 235 then 30 else 60)) else (if i.val < 238 then (if i.val < 237 then 92 else 90) else (if i.val < 239 then 30 else 16)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 29 else 66) else (if i.val < 243 then 30 else 60)) else (if i.val < 246 then (if i.val < 245 then 92 else 66) else (if i.val < 247 then 63 else 34))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 30 else 61) else (if i.val < 251 then 66 else 30)) else (if i.val < 254 then (if i.val < 253 then 62 else 87) else (if i.val < 255 then 60 else 62))))))))

theorem g32p_supplierForest_actual_051 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_051 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_051 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_118365
  · exact g32p_supplierForest_actual_118391
  · exact g32p_supplierForest_actual_118398
  · exact g32p_supplierForest_actual_118412
  · exact g32p_supplierForest_actual_118465
  · exact g32p_supplierForest_actual_118469
  · exact g32p_supplierForest_actual_118481
  · exact g32p_supplierForest_actual_118491
  · exact g32p_supplierForest_actual_118501
  · exact g32p_supplierForest_actual_118527
  · exact g32p_supplierForest_actual_118529
  · exact g32p_supplierForest_actual_118548
  · exact g32p_supplierForest_actual_118570
  · exact g32p_supplierForest_actual_118579
  · exact g32p_supplierForest_actual_118644
  · exact g32p_supplierForest_actual_118654
  · exact g32p_supplierForest_actual_118676
  · exact g32p_supplierForest_actual_118682
  · exact g32p_supplierForest_actual_118702
  · exact g32p_supplierForest_actual_118708
  · exact g32p_supplierForest_actual_118731
  · exact g32p_supplierForest_actual_118848
  · exact g32p_supplierForest_actual_118862
  · exact g32p_supplierForest_actual_118872
  · exact g32p_supplierForest_actual_118880
  · exact g32p_supplierForest_actual_118922
  · exact g32p_supplierForest_actual_119000
  · exact g32p_supplierForest_actual_119019
  · exact g32p_supplierForest_actual_119088
  · exact g32p_supplierForest_actual_119089
  · exact g32p_supplierForest_actual_119167
  · exact g32p_supplierForest_actual_119261
  · exact g32p_supplierForest_actual_119303
  · exact g32p_supplierForest_actual_119321
  · exact g32p_supplierForest_actual_119327
  · exact g32p_supplierForest_actual_119369
  · exact g32p_supplierForest_actual_119386
  · exact g32p_supplierForest_actual_119390
  · exact g32p_supplierForest_actual_119404
  · exact g32p_supplierForest_actual_119426
  · exact g32p_supplierForest_actual_119429
  · exact g32p_supplierForest_actual_119430
  · exact g32p_supplierForest_actual_119438
  · exact g32p_supplierForest_actual_119440
  · exact g32p_supplierForest_actual_119517
  · exact g32p_supplierForest_actual_119571
  · exact g32p_supplierForest_actual_119593
  · exact g32p_supplierForest_actual_119602
  · exact g32p_supplierForest_actual_119607
  · exact g32p_supplierForest_actual_119695
  · exact g32p_supplierForest_actual_119731
  · exact g32p_supplierForest_actual_119759
  · exact g32p_supplierForest_actual_119828
  · exact g32p_supplierForest_actual_119884
  · exact g32p_supplierForest_actual_119909
  · exact g32p_supplierForest_actual_119912
  · exact g32p_supplierForest_actual_119960
  · exact g32p_supplierForest_actual_119970
  · exact g32p_supplierForest_actual_119972
  · exact g32p_supplierForest_actual_120040
  · exact g32p_supplierForest_actual_120041
  · exact g32p_supplierForest_actual_120057
  · exact g32p_supplierForest_actual_120062
  · exact g32p_supplierForest_actual_120129
  · exact g32p_supplierForest_actual_120139
  · exact g32p_supplierForest_actual_120158
  · exact g32p_supplierForest_actual_120182
  · exact g32p_supplierForest_actual_120219
  · exact g32p_supplierForest_actual_120220
  · exact g32p_supplierForest_actual_120222
  · exact g32p_supplierForest_actual_120260
  · exact g32p_supplierForest_actual_120279
  · exact g32p_supplierForest_actual_120309
  · exact g32p_supplierForest_actual_120313
  · exact g32p_supplierForest_actual_120314
  · exact g32p_supplierForest_actual_120354
  · exact g32p_supplierForest_actual_120375
  · exact g32p_supplierForest_actual_120389
  · exact g32p_supplierForest_actual_120465
  · exact g32p_supplierForest_actual_120469
  · exact g32p_supplierForest_actual_120481
  · exact g32p_supplierForest_actual_120486
  · exact g32p_supplierForest_actual_120548
  · exact g32p_supplierForest_actual_120603
  · exact g32p_supplierForest_actual_120751
  · exact g32p_supplierForest_actual_120752
  · exact g32p_supplierForest_actual_120755
  · exact g32p_supplierForest_actual_120779
  · exact g32p_supplierForest_actual_120803
  · exact g32p_supplierForest_actual_120854
  · exact g32p_supplierForest_actual_120876
  · exact g32p_supplierForest_actual_120893
  · exact g32p_supplierForest_actual_120906
  · exact g32p_supplierForest_actual_120933
  · exact g32p_supplierForest_actual_120942
  · exact g32p_supplierForest_actual_120951
  · exact g32p_supplierForest_actual_121001
  · exact g32p_supplierForest_actual_121120
  · exact g32p_supplierForest_actual_121180
  · exact g32p_supplierForest_actual_121191
  · exact g32p_supplierForest_actual_121230
  · exact g32p_supplierForest_actual_121249
  · exact g32p_supplierForest_actual_121260
  · exact g32p_supplierForest_actual_121261
  · exact g32p_supplierForest_actual_121369
  · exact g32p_supplierForest_actual_121410
  · exact g32p_supplierForest_actual_121415
  · exact g32p_supplierForest_actual_121424
  · exact g32p_supplierForest_actual_121434
  · exact g32p_supplierForest_actual_121443
  · exact g32p_supplierForest_actual_121522
  · exact g32p_supplierForest_actual_121567
  · exact g32p_supplierForest_actual_121642
  · exact g32p_supplierForest_actual_121697
  · exact g32p_supplierForest_actual_121712
  · exact g32p_supplierForest_actual_121733
  · exact g32p_supplierForest_actual_121793
  · exact g32p_supplierForest_actual_121833
  · exact g32p_supplierForest_actual_121854
  · exact g32p_supplierForest_actual_121866
  · exact g32p_supplierForest_actual_121880
  · exact g32p_supplierForest_actual_121899
  · exact g32p_supplierForest_actual_121935
  · exact g32p_supplierForest_actual_121999
  · exact g32p_supplierForest_actual_122023
  · exact g32p_supplierForest_actual_122025
  · exact g32p_supplierForest_actual_122044
  · exact g32p_supplierForest_actual_122047
  · exact g32p_supplierForest_actual_122083
  · exact g32p_supplierForest_actual_122088
  · exact g32p_supplierForest_actual_122111
  · exact g32p_supplierForest_actual_122124
  · exact g32p_supplierForest_actual_122167
  · exact g32p_supplierForest_actual_122168
  · exact g32p_supplierForest_actual_122174
  · exact g32p_supplierForest_actual_122188
  · exact g32p_supplierForest_actual_122190
  · exact g32p_supplierForest_actual_122240
  · exact g32p_supplierForest_actual_122244
  · exact g32p_supplierForest_actual_122268
  · exact g32p_supplierForest_actual_122270
  · exact g32p_supplierForest_actual_122286
  · exact g32p_supplierForest_actual_122316
  · exact g32p_supplierForest_actual_122323
  · exact g32p_supplierForest_actual_122334
  · exact g32p_supplierForest_actual_122349
  · exact g32p_supplierForest_actual_122365
  · exact g32p_supplierForest_actual_122366
  · exact g32p_supplierForest_actual_122367
  · exact g32p_supplierForest_actual_122383
  · exact g32p_supplierForest_actual_122385
  · exact g32p_supplierForest_actual_122409
  · exact g32p_supplierForest_actual_122422
  · exact g32p_supplierForest_actual_122442
  · exact g32p_supplierForest_actual_122480
  · exact g32p_supplierForest_actual_122505
  · exact g32p_supplierForest_actual_122532
  · exact g32p_supplierForest_actual_122556
  · exact g32p_supplierForest_actual_122570
  · exact g32p_supplierForest_actual_122626
  · exact g32p_supplierForest_actual_122637
  · exact g32p_supplierForest_actual_122648
  · exact g32p_supplierForest_actual_122665
  · exact g32p_supplierForest_actual_122670
  · exact g32p_supplierForest_actual_122689
  · exact g32p_supplierForest_actual_122708
  · exact g32p_supplierForest_actual_122715
  · exact g32p_supplierForest_actual_122718
  · exact g32p_supplierForest_actual_122728
  · exact g32p_supplierForest_actual_122761
  · exact g32p_supplierForest_actual_122764
  · exact g32p_supplierForest_actual_122868
  · exact g32p_supplierForest_actual_122896
  · exact g32p_supplierForest_actual_122904
  · exact g32p_supplierForest_actual_122927
  · exact g32p_supplierForest_actual_122951
  · exact g32p_supplierForest_actual_122965
  · exact g32p_supplierForest_actual_122974
  · exact g32p_supplierForest_actual_123066
  · exact g32p_supplierForest_actual_123115
  · exact g32p_supplierForest_actual_123125
  · exact g32p_supplierForest_actual_123143
  · exact g32p_supplierForest_actual_123175
  · exact g32p_supplierForest_actual_123189
  · exact g32p_supplierForest_actual_123233
  · exact g32p_supplierForest_actual_123288
  · exact g32p_supplierForest_actual_123333
  · exact g32p_supplierForest_actual_123355
  · exact g32p_supplierForest_actual_123356
  · exact g32p_supplierForest_actual_123387
  · exact g32p_supplierForest_actual_123403
  · exact g32p_supplierForest_actual_123409
  · exact g32p_supplierForest_actual_123449
  · exact g32p_supplierForest_actual_123563
  · exact g32p_supplierForest_actual_123568
  · exact g32p_supplierForest_actual_123570
  · exact g32p_supplierForest_actual_123582
  · exact g32p_supplierForest_actual_123598
  · exact g32p_supplierForest_actual_123601
  · exact g32p_supplierForest_actual_123629
  · exact g32p_supplierForest_actual_123642
  · exact g32p_supplierForest_actual_123654
  · exact g32p_supplierForest_actual_123672
  · exact g32p_supplierForest_actual_123680
  · exact g32p_supplierForest_actual_123686
  · exact g32p_supplierForest_actual_123728
  · exact g32p_supplierForest_actual_123751
  · exact g32p_supplierForest_actual_123797
  · exact g32p_supplierForest_actual_123820
  · exact g32p_supplierForest_actual_123834
  · exact g32p_supplierForest_actual_123847
  · exact g32p_supplierForest_actual_123870
  · exact g32p_supplierForest_actual_123922
  · exact g32p_supplierForest_actual_123929
  · exact g32p_supplierForest_actual_123977
  · exact g32p_supplierForest_actual_123996
  · exact g32p_supplierForest_actual_124014
  · exact g32p_supplierForest_actual_124074
  · exact g32p_supplierForest_actual_124082
  · exact g32p_supplierForest_actual_124087
  · exact g32p_supplierForest_actual_124106
  · exact g32p_supplierForest_actual_124110
  · exact g32p_supplierForest_actual_124114
  · exact g32p_supplierForest_actual_124209
  · exact g32p_supplierForest_actual_124221
  · exact g32p_supplierForest_actual_124263
  · exact g32p_supplierForest_actual_124294
  · exact g32p_supplierForest_actual_124295
  · exact g32p_supplierForest_actual_124322
  · exact g32p_supplierForest_actual_124351
  · exact g32p_supplierForest_actual_124354
  · exact g32p_supplierForest_actual_124374
  · exact g32p_supplierForest_actual_124388
  · exact g32p_supplierForest_actual_124405
  · exact g32p_supplierForest_actual_124421
  · exact g32p_supplierForest_actual_124425
  · exact g32p_supplierForest_actual_124431
  · exact g32p_supplierForest_actual_124435
  · exact g32p_supplierForest_actual_124444
  · exact g32p_supplierForest_actual_124469
  · exact g32p_supplierForest_actual_124513
  · exact g32p_supplierForest_actual_124538
  · exact g32p_supplierForest_actual_124671
  · exact g32p_supplierForest_actual_124751
  · exact g32p_supplierForest_actual_124832
  · exact g32p_supplierForest_actual_124890
  · exact g32p_supplierForest_actual_124892
  · exact g32p_supplierForest_actual_124923
  · exact g32p_supplierForest_actual_124944
  · exact g32p_supplierForest_actual_124951
  · exact g32p_supplierForest_actual_124952
  · exact g32p_supplierForest_actual_124953
  · exact g32p_supplierForest_actual_124960
  · exact g32p_supplierForest_actual_124983
  · exact g32p_supplierForest_actual_124995
  · exact g32p_supplierForest_actual_124997

def g32p_supplierForest_nodes_052 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_125014 else g32p_supplierForest_node_125018) else (if i.val < 3 then g32p_supplierForest_node_125021 else g32p_supplierForest_node_125078)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_125102 else g32p_supplierForest_node_125132) else (if i.val < 7 then g32p_supplierForest_node_125220 else g32p_supplierForest_node_125233))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_125340 else g32p_supplierForest_node_125379) else (if i.val < 11 then g32p_supplierForest_node_125477 else g32p_supplierForest_node_125503)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_125530 else g32p_supplierForest_node_125533) else (if i.val < 15 then g32p_supplierForest_node_125549 else g32p_supplierForest_node_125550)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_125581 else g32p_supplierForest_node_125617) else (if i.val < 19 then g32p_supplierForest_node_125636 else g32p_supplierForest_node_125700)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_125778 else g32p_supplierForest_node_125796) else (if i.val < 23 then g32p_supplierForest_node_125862 else g32p_supplierForest_node_125865))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_125944 else g32p_supplierForest_node_125963) else (if i.val < 27 then g32p_supplierForest_node_125965 else g32p_supplierForest_node_126033)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_126041 else g32p_supplierForest_node_126052) else (if i.val < 31 then g32p_supplierForest_node_126054 else g32p_supplierForest_node_126066))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_126090 else g32p_supplierForest_node_126114) else (if i.val < 35 then g32p_supplierForest_node_126122 else g32p_supplierForest_node_126154)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_126185 else g32p_supplierForest_node_126189) else (if i.val < 39 then g32p_supplierForest_node_126245 else g32p_supplierForest_node_126246))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_126285 else g32p_supplierForest_node_126329) else (if i.val < 43 then g32p_supplierForest_node_126342 else g32p_supplierForest_node_126383)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_126551 else g32p_supplierForest_node_126557) else (if i.val < 47 then g32p_supplierForest_node_126692 else g32p_supplierForest_node_126741)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_126751 else g32p_supplierForest_node_126801) else (if i.val < 51 then g32p_supplierForest_node_126811 else g32p_supplierForest_node_126825)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_126837 else g32p_supplierForest_node_126938) else (if i.val < 55 then g32p_supplierForest_node_126941 else g32p_supplierForest_node_126942))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_126943 else g32p_supplierForest_node_126946) else (if i.val < 59 then g32p_supplierForest_node_126948 else g32p_supplierForest_node_126969)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_127007 else g32p_supplierForest_node_127024) else (if i.val < 63 then g32p_supplierForest_node_127031 else g32p_supplierForest_node_127138)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_127175 else g32p_supplierForest_node_127221) else (if i.val < 67 then g32p_supplierForest_node_127227 else g32p_supplierForest_node_127246)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_127281 else g32p_supplierForest_node_127299) else (if i.val < 71 then g32p_supplierForest_node_127360 else g32p_supplierForest_node_127362))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_127363 else g32p_supplierForest_node_127387) else (if i.val < 75 then g32p_supplierForest_node_127390 else g32p_supplierForest_node_127399)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_127431 else g32p_supplierForest_node_127467) else (if i.val < 79 then g32p_supplierForest_node_127478 else g32p_supplierForest_node_127490)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_127527 else g32p_supplierForest_node_127528) else (if i.val < 83 then g32p_supplierForest_node_127571 else g32p_supplierForest_node_127658)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_127668 else g32p_supplierForest_node_127687) else (if i.val < 87 then g32p_supplierForest_node_127699 else g32p_supplierForest_node_127722))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_127778 else g32p_supplierForest_node_127787) else (if i.val < 91 then g32p_supplierForest_node_127801 else g32p_supplierForest_node_127802)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_127815 else g32p_supplierForest_node_127844) else (if i.val < 95 then g32p_supplierForest_node_127861 else g32p_supplierForest_node_127896))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_127958 else g32p_supplierForest_node_127968) else (if i.val < 99 then g32p_supplierForest_node_128009 else g32p_supplierForest_node_128012)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_128039 else g32p_supplierForest_node_128047) else (if i.val < 103 then g32p_supplierForest_node_128051 else g32p_supplierForest_node_128085))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_128099 else g32p_supplierForest_node_128125) else (if i.val < 107 then g32p_supplierForest_node_128127 else g32p_supplierForest_node_128135)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_128236 else g32p_supplierForest_node_128253) else (if i.val < 111 then g32p_supplierForest_node_128273 else g32p_supplierForest_node_128277)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_128282 else g32p_supplierForest_node_128309) else (if i.val < 115 then g32p_supplierForest_node_128329 else g32p_supplierForest_node_128342)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_128354 else g32p_supplierForest_node_128365) else (if i.val < 119 then g32p_supplierForest_node_128390 else g32p_supplierForest_node_128392))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_128400 else g32p_supplierForest_node_128401) else (if i.val < 123 then g32p_supplierForest_node_128430 else g32p_supplierForest_node_128436)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_128452 else g32p_supplierForest_node_128455) else (if i.val < 127 then g32p_supplierForest_node_128460 else g32p_supplierForest_node_128473))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_128500 else g32p_supplierForest_node_128530) else (if i.val < 131 then g32p_supplierForest_node_128543 else g32p_supplierForest_node_128547)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_128570 else g32p_supplierForest_node_128577) else (if i.val < 135 then g32p_supplierForest_node_128581 else g32p_supplierForest_node_128614))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_128623 else g32p_supplierForest_node_128640) else (if i.val < 139 then g32p_supplierForest_node_128684 else g32p_supplierForest_node_128721)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_128726 else g32p_supplierForest_node_128781) else (if i.val < 143 then g32p_supplierForest_node_128806 else g32p_supplierForest_node_128848)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_128855 else g32p_supplierForest_node_128886) else (if i.val < 147 then g32p_supplierForest_node_128911 else g32p_supplierForest_node_128952)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_128970 else g32p_supplierForest_node_129017) else (if i.val < 151 then g32p_supplierForest_node_129042 else g32p_supplierForest_node_129094))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_129143 else g32p_supplierForest_node_129160) else (if i.val < 155 then g32p_supplierForest_node_129170 else g32p_supplierForest_node_129202)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_129219 else g32p_supplierForest_node_129252) else (if i.val < 159 then g32p_supplierForest_node_129299 else g32p_supplierForest_node_129343))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_129368 else g32p_supplierForest_node_129395) else (if i.val < 163 then g32p_supplierForest_node_129400 else g32p_supplierForest_node_129447)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_129456 else g32p_supplierForest_node_129518) else (if i.val < 167 then g32p_supplierForest_node_129532 else g32p_supplierForest_node_129538))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_129556 else g32p_supplierForest_node_129567) else (if i.val < 171 then g32p_supplierForest_node_129582 else g32p_supplierForest_node_129598)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_129651 else g32p_supplierForest_node_129653) else (if i.val < 175 then g32p_supplierForest_node_129719 else g32p_supplierForest_node_129743)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_129781 else g32p_supplierForest_node_129821) else (if i.val < 179 then g32p_supplierForest_node_129851 else g32p_supplierForest_node_129878)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_129936 else g32p_supplierForest_node_129953) else (if i.val < 183 then g32p_supplierForest_node_129970 else g32p_supplierForest_node_129974))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_129999 else g32p_supplierForest_node_130041) else (if i.val < 187 then g32p_supplierForest_node_130059 else g32p_supplierForest_node_130068)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_130108 else g32p_supplierForest_node_130126) else (if i.val < 191 then g32p_supplierForest_node_130134 else g32p_supplierForest_node_130154)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_130208 else g32p_supplierForest_node_130224) else (if i.val < 195 then g32p_supplierForest_node_130241 else g32p_supplierForest_node_130257)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_130288 else g32p_supplierForest_node_130302) else (if i.val < 199 then g32p_supplierForest_node_130348 else g32p_supplierForest_node_130394))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_130395 else g32p_supplierForest_node_130428) else (if i.val < 203 then g32p_supplierForest_node_130438 else g32p_supplierForest_node_130450)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_130459 else g32p_supplierForest_node_130510) else (if i.val < 207 then g32p_supplierForest_node_130580 else g32p_supplierForest_node_130607)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_130660 else g32p_supplierForest_node_130688) else (if i.val < 211 then g32p_supplierForest_node_130770 else g32p_supplierForest_node_130807)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_130808 else g32p_supplierForest_node_130813) else (if i.val < 215 then g32p_supplierForest_node_130828 else g32p_supplierForest_node_130836))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_130837 else g32p_supplierForest_node_130843) else (if i.val < 219 then g32p_supplierForest_node_130848 else g32p_supplierForest_node_130852)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_130855 else g32p_supplierForest_node_130917) else (if i.val < 223 then g32p_supplierForest_node_130936 else g32p_supplierForest_node_130940))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_130948 else g32p_supplierForest_node_130955) else (if i.val < 227 then g32p_supplierForest_node_130966 else g32p_supplierForest_node_130978)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_131008 else g32p_supplierForest_node_131060) else (if i.val < 231 then g32p_supplierForest_node_131114 else g32p_supplierForest_node_131132))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_131151 else g32p_supplierForest_node_131155) else (if i.val < 235 then g32p_supplierForest_node_131247 else g32p_supplierForest_node_131261)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_131262 else g32p_supplierForest_node_131263) else (if i.val < 239 then g32p_supplierForest_node_131305 else g32p_supplierForest_node_131330)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_131344 else g32p_supplierForest_node_131346) else (if i.val < 243 then g32p_supplierForest_node_131353 else g32p_supplierForest_node_131395)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_131396 else g32p_supplierForest_node_131402) else (if i.val < 247 then g32p_supplierForest_node_131414 else g32p_supplierForest_node_131467))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_131500 else g32p_supplierForest_node_131541) else (if i.val < 251 then g32p_supplierForest_node_131577 else g32p_supplierForest_node_131633)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_131703 else g32p_supplierForest_node_131755) else (if i.val < 255 then g32p_supplierForest_node_131850 else g32p_supplierForest_node_131868))))))))

def g32p_supplierForest_classes_052 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 60 else 58) else (if i.val < 3 then 63 else 35)) else (if i.val < 6 then (if i.val < 5 then 34 else 60) else (if i.val < 7 then 63 else 61))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 61 else 61) else (if i.val < 11 then 58 else 35)) else (if i.val < 14 then (if i.val < 13 then 33 else 91) else (if i.val < 15 then 89 else 89)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 90 else 63) else (if i.val < 19 then 59 else 89)) else (if i.val < 22 then (if i.val < 21 then 33 else 30) else (if i.val < 23 then 89 else 30))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 90 else 90) else (if i.val < 27 then 61 else 57)) else (if i.val < 30 then (if i.val < 29 then 34 else 60) else (if i.val < 31 then 61 else 60))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 60 else 65) else (if i.val < 35 then 66 else 30)) else (if i.val < 38 then (if i.val < 37 then 35 else 91) else (if i.val < 39 then 91 else 35))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 59 else 35) else (if i.val < 43 then 59 else 63)) else (if i.val < 46 then (if i.val < 45 then 30 else 90) else (if i.val < 47 then 92 else 92)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 58 else 57) else (if i.val < 51 then 62 else 66)) else (if i.val < 54 then (if i.val < 53 then 93 else 35) else (if i.val < 55 then 90 else 30))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 35 else 92) else (if i.val < 59 then 33 else 92)) else (if i.val < 62 then (if i.val < 61 then 61 else 30) else (if i.val < 63 then 60 else 62)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 60 else 58) else (if i.val < 67 then 61 else 60)) else (if i.val < 70 then (if i.val < 69 then 57 else 92) else (if i.val < 71 then 91 else 90))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 30 else 92) else (if i.val < 75 then 35 else 60)) else (if i.val < 78 then (if i.val < 77 then 90 else 90) else (if i.val < 79 then 34 else 63)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 59 else 35) else (if i.val < 83 then 34 else 35)) else (if i.val < 86 then (if i.val < 85 then 66 else 90) else (if i.val < 87 then 92 else 30))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 87 else 57) else (if i.val < 91 then 90 else 60)) else (if i.val < 94 then (if i.val < 93 then 41 else 73) else (if i.val < 95 then 68 else 73))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 21 else 71) else (if i.val < 99 then 70 else 73)) else (if i.val < 102 then (if i.val < 101 then 74 else 71) else (if i.val < 103 then 21 else 73))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 38 else 73) else (if i.val < 107 then 22 else 42)) else (if i.val < 110 then (if i.val < 109 then 43 else 74) else (if i.val < 111 then 21 else 68)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 71 else 74) else (if i.val < 115 then 70 else 41)) else (if i.val < 118 then (if i.val < 117 then 74 else 70) else (if i.val < 119 then 72 else 73))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 73 else 79) else (if i.val < 123 then 74 else 68)) else (if i.val < 126 then (if i.val < 125 then 70 else 69) else (if i.val < 127 then 74 else 71))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 38 else 71) else (if i.val < 131 then 75 else 78)) else (if i.val < 134 then (if i.val < 133 then 21 else 94) else (if i.val < 135 then 68 else 18))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 43 else 18) else (if i.val < 139 then 69 else 42)) else (if i.val < 142 then (if i.val < 141 then 74 else 72) else (if i.val < 143 then 40 else 43)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 67 else 79) else (if i.val < 147 then 69 else 43)) else (if i.val < 150 then (if i.val < 149 then 42 else 69) else (if i.val < 151 then 73 else 38))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 68 else 69) else (if i.val < 155 then 69 else 41)) else (if i.val < 158 then (if i.val < 157 then 74 else 72) else (if i.val < 159 then 41 else 38))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 73 else 74) else (if i.val < 163 then 94 else 79)) else (if i.val < 166 then (if i.val < 165 then 74 else 18) else (if i.val < 167 then 43 else 69))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 22 else 69) else (if i.val < 171 then 72 else 70)) else (if i.val < 174 then (if i.val < 173 then 43 else 20) else (if i.val < 175 then 71 else 73)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 67 else 73) else (if i.val < 179 then 38 else 69)) else (if i.val < 182 then (if i.val < 181 then 42 else 38) else (if i.val < 183 then 73 else 18))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 72 else 21) else (if i.val < 187 then 20 else 71)) else (if i.val < 190 then (if i.val < 189 then 42 else 73) else (if i.val < 191 then 43 else 73)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 38 else 38) else (if i.val < 195 then 69 else 38)) else (if i.val < 198 then (if i.val < 197 then 38 else 71) else (if i.val < 199 then 69 else 40))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 40 else 38) else (if i.val < 203 then 38 else 38)) else (if i.val < 206 then (if i.val < 205 then 68 else 38) else (if i.val < 207 then 21 else 73)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 38 else 40) else (if i.val < 211 then 18 else 71)) else (if i.val < 214 then (if i.val < 213 then 71 else 71) else (if i.val < 215 then 71 else 42))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 71 else 71) else (if i.val < 219 then 71 else 38)) else (if i.val < 222 then (if i.val < 221 then 71 else 74) else (if i.val < 223 then 71 else 68))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 71 else 38) else (if i.val < 227 then 77 else 74)) else (if i.val < 230 then (if i.val < 229 then 72 else 79) else (if i.val < 231 then 71 else 74))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 73 else 18) else (if i.val < 235 then 74 else 69)) else (if i.val < 238 then (if i.val < 237 then 43 else 69) else (if i.val < 239 then 94 else 38)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 73 else 39) else (if i.val < 243 then 20 else 76)) else (if i.val < 246 then (if i.val < 245 then 38 else 73) else (if i.val < 247 then 77 else 69))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 75 else 74) else (if i.val < 251 then 72 else 94)) else (if i.val < 254 then (if i.val < 253 then 79 else 69) else (if i.val < 255 then 69 else 70))))))))

theorem g32p_supplierForest_actual_052 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_052 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_052 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_125014
  · exact g32p_supplierForest_actual_125018
  · exact g32p_supplierForest_actual_125021
  · exact g32p_supplierForest_actual_125078
  · exact g32p_supplierForest_actual_125102
  · exact g32p_supplierForest_actual_125132
  · exact g32p_supplierForest_actual_125220
  · exact g32p_supplierForest_actual_125233
  · exact g32p_supplierForest_actual_125340
  · exact g32p_supplierForest_actual_125379
  · exact g32p_supplierForest_actual_125477
  · exact g32p_supplierForest_actual_125503
  · exact g32p_supplierForest_actual_125530
  · exact g32p_supplierForest_actual_125533
  · exact g32p_supplierForest_actual_125549
  · exact g32p_supplierForest_actual_125550
  · exact g32p_supplierForest_actual_125581
  · exact g32p_supplierForest_actual_125617
  · exact g32p_supplierForest_actual_125636
  · exact g32p_supplierForest_actual_125700
  · exact g32p_supplierForest_actual_125778
  · exact g32p_supplierForest_actual_125796
  · exact g32p_supplierForest_actual_125862
  · exact g32p_supplierForest_actual_125865
  · exact g32p_supplierForest_actual_125944
  · exact g32p_supplierForest_actual_125963
  · exact g32p_supplierForest_actual_125965
  · exact g32p_supplierForest_actual_126033
  · exact g32p_supplierForest_actual_126041
  · exact g32p_supplierForest_actual_126052
  · exact g32p_supplierForest_actual_126054
  · exact g32p_supplierForest_actual_126066
  · exact g32p_supplierForest_actual_126090
  · exact g32p_supplierForest_actual_126114
  · exact g32p_supplierForest_actual_126122
  · exact g32p_supplierForest_actual_126154
  · exact g32p_supplierForest_actual_126185
  · exact g32p_supplierForest_actual_126189
  · exact g32p_supplierForest_actual_126245
  · exact g32p_supplierForest_actual_126246
  · exact g32p_supplierForest_actual_126285
  · exact g32p_supplierForest_actual_126329
  · exact g32p_supplierForest_actual_126342
  · exact g32p_supplierForest_actual_126383
  · exact g32p_supplierForest_actual_126551
  · exact g32p_supplierForest_actual_126557
  · exact g32p_supplierForest_actual_126692
  · exact g32p_supplierForest_actual_126741
  · exact g32p_supplierForest_actual_126751
  · exact g32p_supplierForest_actual_126801
  · exact g32p_supplierForest_actual_126811
  · exact g32p_supplierForest_actual_126825
  · exact g32p_supplierForest_actual_126837
  · exact g32p_supplierForest_actual_126938
  · exact g32p_supplierForest_actual_126941
  · exact g32p_supplierForest_actual_126942
  · exact g32p_supplierForest_actual_126943
  · exact g32p_supplierForest_actual_126946
  · exact g32p_supplierForest_actual_126948
  · exact g32p_supplierForest_actual_126969
  · exact g32p_supplierForest_actual_127007
  · exact g32p_supplierForest_actual_127024
  · exact g32p_supplierForest_actual_127031
  · exact g32p_supplierForest_actual_127138
  · exact g32p_supplierForest_actual_127175
  · exact g32p_supplierForest_actual_127221
  · exact g32p_supplierForest_actual_127227
  · exact g32p_supplierForest_actual_127246
  · exact g32p_supplierForest_actual_127281
  · exact g32p_supplierForest_actual_127299
  · exact g32p_supplierForest_actual_127360
  · exact g32p_supplierForest_actual_127362
  · exact g32p_supplierForest_actual_127363
  · exact g32p_supplierForest_actual_127387
  · exact g32p_supplierForest_actual_127390
  · exact g32p_supplierForest_actual_127399
  · exact g32p_supplierForest_actual_127431
  · exact g32p_supplierForest_actual_127467
  · exact g32p_supplierForest_actual_127478
  · exact g32p_supplierForest_actual_127490
  · exact g32p_supplierForest_actual_127527
  · exact g32p_supplierForest_actual_127528
  · exact g32p_supplierForest_actual_127571
  · exact g32p_supplierForest_actual_127658
  · exact g32p_supplierForest_actual_127668
  · exact g32p_supplierForest_actual_127687
  · exact g32p_supplierForest_actual_127699
  · exact g32p_supplierForest_actual_127722
  · exact g32p_supplierForest_actual_127778
  · exact g32p_supplierForest_actual_127787
  · exact g32p_supplierForest_actual_127801
  · exact g32p_supplierForest_actual_127802
  · exact g32p_supplierForest_actual_127815
  · exact g32p_supplierForest_actual_127844
  · exact g32p_supplierForest_actual_127861
  · exact g32p_supplierForest_actual_127896
  · exact g32p_supplierForest_actual_127958
  · exact g32p_supplierForest_actual_127968
  · exact g32p_supplierForest_actual_128009
  · exact g32p_supplierForest_actual_128012
  · exact g32p_supplierForest_actual_128039
  · exact g32p_supplierForest_actual_128047
  · exact g32p_supplierForest_actual_128051
  · exact g32p_supplierForest_actual_128085
  · exact g32p_supplierForest_actual_128099
  · exact g32p_supplierForest_actual_128125
  · exact g32p_supplierForest_actual_128127
  · exact g32p_supplierForest_actual_128135
  · exact g32p_supplierForest_actual_128236
  · exact g32p_supplierForest_actual_128253
  · exact g32p_supplierForest_actual_128273
  · exact g32p_supplierForest_actual_128277
  · exact g32p_supplierForest_actual_128282
  · exact g32p_supplierForest_actual_128309
  · exact g32p_supplierForest_actual_128329
  · exact g32p_supplierForest_actual_128342
  · exact g32p_supplierForest_actual_128354
  · exact g32p_supplierForest_actual_128365
  · exact g32p_supplierForest_actual_128390
  · exact g32p_supplierForest_actual_128392
  · exact g32p_supplierForest_actual_128400
  · exact g32p_supplierForest_actual_128401
  · exact g32p_supplierForest_actual_128430
  · exact g32p_supplierForest_actual_128436
  · exact g32p_supplierForest_actual_128452
  · exact g32p_supplierForest_actual_128455
  · exact g32p_supplierForest_actual_128460
  · exact g32p_supplierForest_actual_128473
  · exact g32p_supplierForest_actual_128500
  · exact g32p_supplierForest_actual_128530
  · exact g32p_supplierForest_actual_128543
  · exact g32p_supplierForest_actual_128547
  · exact g32p_supplierForest_actual_128570
  · exact g32p_supplierForest_actual_128577
  · exact g32p_supplierForest_actual_128581
  · exact g32p_supplierForest_actual_128614
  · exact g32p_supplierForest_actual_128623
  · exact g32p_supplierForest_actual_128640
  · exact g32p_supplierForest_actual_128684
  · exact g32p_supplierForest_actual_128721
  · exact g32p_supplierForest_actual_128726
  · exact g32p_supplierForest_actual_128781
  · exact g32p_supplierForest_actual_128806
  · exact g32p_supplierForest_actual_128848
  · exact g32p_supplierForest_actual_128855
  · exact g32p_supplierForest_actual_128886
  · exact g32p_supplierForest_actual_128911
  · exact g32p_supplierForest_actual_128952
  · exact g32p_supplierForest_actual_128970
  · exact g32p_supplierForest_actual_129017
  · exact g32p_supplierForest_actual_129042
  · exact g32p_supplierForest_actual_129094
  · exact g32p_supplierForest_actual_129143
  · exact g32p_supplierForest_actual_129160
  · exact g32p_supplierForest_actual_129170
  · exact g32p_supplierForest_actual_129202
  · exact g32p_supplierForest_actual_129219
  · exact g32p_supplierForest_actual_129252
  · exact g32p_supplierForest_actual_129299
  · exact g32p_supplierForest_actual_129343
  · exact g32p_supplierForest_actual_129368
  · exact g32p_supplierForest_actual_129395
  · exact g32p_supplierForest_actual_129400
  · exact g32p_supplierForest_actual_129447
  · exact g32p_supplierForest_actual_129456
  · exact g32p_supplierForest_actual_129518
  · exact g32p_supplierForest_actual_129532
  · exact g32p_supplierForest_actual_129538
  · exact g32p_supplierForest_actual_129556
  · exact g32p_supplierForest_actual_129567
  · exact g32p_supplierForest_actual_129582
  · exact g32p_supplierForest_actual_129598
  · exact g32p_supplierForest_actual_129651
  · exact g32p_supplierForest_actual_129653
  · exact g32p_supplierForest_actual_129719
  · exact g32p_supplierForest_actual_129743
  · exact g32p_supplierForest_actual_129781
  · exact g32p_supplierForest_actual_129821
  · exact g32p_supplierForest_actual_129851
  · exact g32p_supplierForest_actual_129878
  · exact g32p_supplierForest_actual_129936
  · exact g32p_supplierForest_actual_129953
  · exact g32p_supplierForest_actual_129970
  · exact g32p_supplierForest_actual_129974
  · exact g32p_supplierForest_actual_129999
  · exact g32p_supplierForest_actual_130041
  · exact g32p_supplierForest_actual_130059
  · exact g32p_supplierForest_actual_130068
  · exact g32p_supplierForest_actual_130108
  · exact g32p_supplierForest_actual_130126
  · exact g32p_supplierForest_actual_130134
  · exact g32p_supplierForest_actual_130154
  · exact g32p_supplierForest_actual_130208
  · exact g32p_supplierForest_actual_130224
  · exact g32p_supplierForest_actual_130241
  · exact g32p_supplierForest_actual_130257
  · exact g32p_supplierForest_actual_130288
  · exact g32p_supplierForest_actual_130302
  · exact g32p_supplierForest_actual_130348
  · exact g32p_supplierForest_actual_130394
  · exact g32p_supplierForest_actual_130395
  · exact g32p_supplierForest_actual_130428
  · exact g32p_supplierForest_actual_130438
  · exact g32p_supplierForest_actual_130450
  · exact g32p_supplierForest_actual_130459
  · exact g32p_supplierForest_actual_130510
  · exact g32p_supplierForest_actual_130580
  · exact g32p_supplierForest_actual_130607
  · exact g32p_supplierForest_actual_130660
  · exact g32p_supplierForest_actual_130688
  · exact g32p_supplierForest_actual_130770
  · exact g32p_supplierForest_actual_130807
  · exact g32p_supplierForest_actual_130808
  · exact g32p_supplierForest_actual_130813
  · exact g32p_supplierForest_actual_130828
  · exact g32p_supplierForest_actual_130836
  · exact g32p_supplierForest_actual_130837
  · exact g32p_supplierForest_actual_130843
  · exact g32p_supplierForest_actual_130848
  · exact g32p_supplierForest_actual_130852
  · exact g32p_supplierForest_actual_130855
  · exact g32p_supplierForest_actual_130917
  · exact g32p_supplierForest_actual_130936
  · exact g32p_supplierForest_actual_130940
  · exact g32p_supplierForest_actual_130948
  · exact g32p_supplierForest_actual_130955
  · exact g32p_supplierForest_actual_130966
  · exact g32p_supplierForest_actual_130978
  · exact g32p_supplierForest_actual_131008
  · exact g32p_supplierForest_actual_131060
  · exact g32p_supplierForest_actual_131114
  · exact g32p_supplierForest_actual_131132
  · exact g32p_supplierForest_actual_131151
  · exact g32p_supplierForest_actual_131155
  · exact g32p_supplierForest_actual_131247
  · exact g32p_supplierForest_actual_131261
  · exact g32p_supplierForest_actual_131262
  · exact g32p_supplierForest_actual_131263
  · exact g32p_supplierForest_actual_131305
  · exact g32p_supplierForest_actual_131330
  · exact g32p_supplierForest_actual_131344
  · exact g32p_supplierForest_actual_131346
  · exact g32p_supplierForest_actual_131353
  · exact g32p_supplierForest_actual_131395
  · exact g32p_supplierForest_actual_131396
  · exact g32p_supplierForest_actual_131402
  · exact g32p_supplierForest_actual_131414
  · exact g32p_supplierForest_actual_131467
  · exact g32p_supplierForest_actual_131500
  · exact g32p_supplierForest_actual_131541
  · exact g32p_supplierForest_actual_131577
  · exact g32p_supplierForest_actual_131633
  · exact g32p_supplierForest_actual_131703
  · exact g32p_supplierForest_actual_131755
  · exact g32p_supplierForest_actual_131850
  · exact g32p_supplierForest_actual_131868

def g32p_supplierForest_nodes_053 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_131959 else g32p_supplierForest_node_131970) else (if i.val < 3 then g32p_supplierForest_node_131988 else g32p_supplierForest_node_131989)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_132009 else g32p_supplierForest_node_132022) else (if i.val < 7 then g32p_supplierForest_node_132036 else g32p_supplierForest_node_132053))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_132055 else g32p_supplierForest_node_132112) else (if i.val < 11 then g32p_supplierForest_node_132115 else g32p_supplierForest_node_132121)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_132144 else g32p_supplierForest_node_132196) else (if i.val < 15 then g32p_supplierForest_node_132212 else g32p_supplierForest_node_132214)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_132230 else g32p_supplierForest_node_132243) else (if i.val < 19 then g32p_supplierForest_node_132280 else g32p_supplierForest_node_132302)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_132358 else g32p_supplierForest_node_132376) else (if i.val < 23 then g32p_supplierForest_node_132383 else g32p_supplierForest_node_132412))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_132452 else g32p_supplierForest_node_132482) else (if i.val < 27 then g32p_supplierForest_node_132491 else g32p_supplierForest_node_132514)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_132569 else g32p_supplierForest_node_132583) else (if i.val < 31 then g32p_supplierForest_node_132639 else g32p_supplierForest_node_132647))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_132655 else g32p_supplierForest_node_132719) else (if i.val < 35 then g32p_supplierForest_node_132741 else g32p_supplierForest_node_132772)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_132778 else g32p_supplierForest_node_132807) else (if i.val < 39 then g32p_supplierForest_node_132888 else g32p_supplierForest_node_132897))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_132905 else g32p_supplierForest_node_132908) else (if i.val < 43 then g32p_supplierForest_node_132992 else g32p_supplierForest_node_133021)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_133041 else g32p_supplierForest_node_133107) else (if i.val < 47 then g32p_supplierForest_node_133131 else g32p_supplierForest_node_133145)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_133146 else g32p_supplierForest_node_133186) else (if i.val < 51 then g32p_supplierForest_node_133215 else g32p_supplierForest_node_133217)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_133226 else g32p_supplierForest_node_133291) else (if i.val < 55 then g32p_supplierForest_node_133334 else g32p_supplierForest_node_133365))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_133396 else g32p_supplierForest_node_133405) else (if i.val < 59 then g32p_supplierForest_node_133439 else g32p_supplierForest_node_133466)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_133506 else g32p_supplierForest_node_133519) else (if i.val < 63 then g32p_supplierForest_node_133522 else g32p_supplierForest_node_133537)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_133558 else g32p_supplierForest_node_133560) else (if i.val < 67 then g32p_supplierForest_node_133575 else g32p_supplierForest_node_133576)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_133588 else g32p_supplierForest_node_133647) else (if i.val < 71 then g32p_supplierForest_node_133694 else g32p_supplierForest_node_133714))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_133729 else g32p_supplierForest_node_133749) else (if i.val < 75 then g32p_supplierForest_node_133770 else g32p_supplierForest_node_133782)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_133783 else g32p_supplierForest_node_133812) else (if i.val < 79 then g32p_supplierForest_node_133820 else g32p_supplierForest_node_133822)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_133824 else g32p_supplierForest_node_133826) else (if i.val < 83 then g32p_supplierForest_node_133836 else g32p_supplierForest_node_133895)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_134015 else g32p_supplierForest_node_134027) else (if i.val < 87 then g32p_supplierForest_node_134037 else g32p_supplierForest_node_134072))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_134079 else g32p_supplierForest_node_134139) else (if i.val < 91 then g32p_supplierForest_node_134141 else g32p_supplierForest_node_134162)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_134165 else g32p_supplierForest_node_134201) else (if i.val < 95 then g32p_supplierForest_node_134252 else g32p_supplierForest_node_134260))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_134287 else g32p_supplierForest_node_134349) else (if i.val < 99 then g32p_supplierForest_node_134397 else g32p_supplierForest_node_134423)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_134440 else g32p_supplierForest_node_134456) else (if i.val < 103 then g32p_supplierForest_node_134557 else g32p_supplierForest_node_134639))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_134640 else g32p_supplierForest_node_134689) else (if i.val < 107 then g32p_supplierForest_node_134691 else g32p_supplierForest_node_134704)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_134746 else g32p_supplierForest_node_134782) else (if i.val < 111 then g32p_supplierForest_node_134795 else g32p_supplierForest_node_134845)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_134854 else g32p_supplierForest_node_134916) else (if i.val < 115 then g32p_supplierForest_node_134931 else g32p_supplierForest_node_134934)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_134936 else g32p_supplierForest_node_134942) else (if i.val < 119 then g32p_supplierForest_node_134973 else g32p_supplierForest_node_134991))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_134993 else g32p_supplierForest_node_134999) else (if i.val < 123 then g32p_supplierForest_node_135034 else g32p_supplierForest_node_135109)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_135121 else g32p_supplierForest_node_135124) else (if i.val < 127 then g32p_supplierForest_node_135130 else g32p_supplierForest_node_135171))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_135196 else g32p_supplierForest_node_135206) else (if i.val < 131 then g32p_supplierForest_node_135218 else g32p_supplierForest_node_135255)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_135365 else g32p_supplierForest_node_135392) else (if i.val < 135 then g32p_supplierForest_node_135395 else g32p_supplierForest_node_135488))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_135501 else g32p_supplierForest_node_135516) else (if i.val < 139 then g32p_supplierForest_node_135557 else g32p_supplierForest_node_135558)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_135572 else g32p_supplierForest_node_135578) else (if i.val < 143 then g32p_supplierForest_node_135609 else g32p_supplierForest_node_135662)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_135679 else g32p_supplierForest_node_135697) else (if i.val < 147 then g32p_supplierForest_node_135788 else g32p_supplierForest_node_135812)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_135831 else g32p_supplierForest_node_135849) else (if i.val < 151 then g32p_supplierForest_node_135868 else g32p_supplierForest_node_135889))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_135897 else g32p_supplierForest_node_135912) else (if i.val < 155 then g32p_supplierForest_node_135921 else g32p_supplierForest_node_135927)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_135984 else g32p_supplierForest_node_135992) else (if i.val < 159 then g32p_supplierForest_node_136002 else g32p_supplierForest_node_136038))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_136166 else g32p_supplierForest_node_136310) else (if i.val < 163 then g32p_supplierForest_node_136353 else g32p_supplierForest_node_136373)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_136445 else g32p_supplierForest_node_136447) else (if i.val < 167 then g32p_supplierForest_node_136456 else g32p_supplierForest_node_136466))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_136471 else g32p_supplierForest_node_136484) else (if i.val < 171 then g32p_supplierForest_node_136652 else g32p_supplierForest_node_136660)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_136677 else g32p_supplierForest_node_136700) else (if i.val < 175 then g32p_supplierForest_node_136757 else g32p_supplierForest_node_136759)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_136794 else g32p_supplierForest_node_136811) else (if i.val < 179 then g32p_supplierForest_node_136873 else g32p_supplierForest_node_136889)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_136933 else g32p_supplierForest_node_136959) else (if i.val < 183 then g32p_supplierForest_node_136960 else g32p_supplierForest_node_136971))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_136985 else g32p_supplierForest_node_137005) else (if i.val < 187 then g32p_supplierForest_node_137032 else g32p_supplierForest_node_137046)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_137149 else g32p_supplierForest_node_137167) else (if i.val < 191 then g32p_supplierForest_node_137169 else g32p_supplierForest_node_137192)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_137199 else g32p_supplierForest_node_137221) else (if i.val < 195 then g32p_supplierForest_node_137223 else g32p_supplierForest_node_137237)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_137249 else g32p_supplierForest_node_137271) else (if i.val < 199 then g32p_supplierForest_node_137286 else g32p_supplierForest_node_137293))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_137296 else g32p_supplierForest_node_137323) else (if i.val < 203 then g32p_supplierForest_node_137367 else g32p_supplierForest_node_137422)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_137502 else g32p_supplierForest_node_137514) else (if i.val < 207 then g32p_supplierForest_node_137572 else g32p_supplierForest_node_137689)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_137702 else g32p_supplierForest_node_137715) else (if i.val < 211 then g32p_supplierForest_node_137739 else g32p_supplierForest_node_137744)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_137778 else g32p_supplierForest_node_137801) else (if i.val < 215 then g32p_supplierForest_node_137838 else g32p_supplierForest_node_137861))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_137879 else g32p_supplierForest_node_137906) else (if i.val < 219 then g32p_supplierForest_node_137943 else g32p_supplierForest_node_137954)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_137964 else g32p_supplierForest_node_137980) else (if i.val < 223 then g32p_supplierForest_node_138002 else g32p_supplierForest_node_138015))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_138045 else g32p_supplierForest_node_138076) else (if i.val < 227 then g32p_supplierForest_node_138083 else g32p_supplierForest_node_138123)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_138134 else g32p_supplierForest_node_138167) else (if i.val < 231 then g32p_supplierForest_node_138193 else g32p_supplierForest_node_138204))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_138299 else g32p_supplierForest_node_138345) else (if i.val < 235 then g32p_supplierForest_node_138425 else g32p_supplierForest_node_138426)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_138432 else g32p_supplierForest_node_138442) else (if i.val < 239 then g32p_supplierForest_node_138445 else g32p_supplierForest_node_138579)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_138636 else g32p_supplierForest_node_138654) else (if i.val < 243 then g32p_supplierForest_node_138659 else g32p_supplierForest_node_138660)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_138679 else g32p_supplierForest_node_138685) else (if i.val < 247 then g32p_supplierForest_node_138701 else g32p_supplierForest_node_138710))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_138719 else g32p_supplierForest_node_138767) else (if i.val < 251 then g32p_supplierForest_node_138808 else g32p_supplierForest_node_138844)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_138887 else g32p_supplierForest_node_138905) else (if i.val < 255 then g32p_supplierForest_node_138941 else g32p_supplierForest_node_138969))))))))

def g32p_supplierForest_classes_053 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 71 else 73) else (if i.val < 3 then 38 else 69)) else (if i.val < 6 then (if i.val < 5 then 73 else 21) else (if i.val < 7 then 42 else 38))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 18 else 43) else (if i.val < 11 then 20 else 75)) else (if i.val < 14 then (if i.val < 13 then 21 else 77) else (if i.val < 15 then 71 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 42 else 18) else (if i.val < 19 then 74 else 69)) else (if i.val < 22 then (if i.val < 21 then 38 else 7) else (if i.val < 23 then 38 else 74))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 71 else 71) else (if i.val < 27 then 42 else 77)) else (if i.val < 30 then (if i.val < 29 then 38 else 73) else (if i.val < 31 then 73 else 21))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 68 else 73) else (if i.val < 35 then 42 else 69)) else (if i.val < 38 then (if i.val < 37 then 69 else 71) else (if i.val < 39 then 43 else 71))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 72 else 74) else (if i.val < 43 then 42 else 75)) else (if i.val < 46 then (if i.val < 45 then 43 else 71) else (if i.val < 47 then 71 else 94)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 20 else 72) else (if i.val < 51 then 77 else 75)) else (if i.val < 54 then (if i.val < 53 then 21 else 21) else (if i.val < 55 then 71 else 75))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 72 else 79) else (if i.val < 59 then 94 else 69)) else (if i.val < 62 then (if i.val < 61 then 74 else 73) else (if i.val < 63 then 68 else 79)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 41 else 78) else (if i.val < 67 then 94 else 75)) else (if i.val < 70 then (if i.val < 69 then 69 else 43) else (if i.val < 71 then 78 else 43))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 69 else 69) else (if i.val < 75 then 21 else 74)) else (if i.val < 78 then (if i.val < 77 then 71 else 73) else (if i.val < 79 then 21 else 20)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 75 else 95) else (if i.val < 83 then 71 else 42)) else (if i.val < 86 then (if i.val < 85 then 38 else 94) else (if i.val < 87 then 94 else 71))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 73 else 69) else (if i.val < 91 then 69 else 70)) else (if i.val < 94 then (if i.val < 93 then 69 else 43) else (if i.val < 95 then 79 else 79))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 78 else 20) else (if i.val < 99 then 73 else 68)) else (if i.val < 102 then (if i.val < 101 then 72 else 73) else (if i.val < 103 then 43 else 69))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 71 else 78) else (if i.val < 107 then 75 else 68)) else (if i.val < 110 then (if i.val < 109 then 95 else 38) else (if i.val < 111 then 72 else 75)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 75 else 40) else (if i.val < 115 then 40 else 78)) else (if i.val < 118 then (if i.val < 117 then 94 else 68) else (if i.val < 119 then 75 else 42))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 73 else 70) else (if i.val < 123 then 73 else 18)) else (if i.val < 126 then (if i.val < 125 then 74 else 69) else (if i.val < 127 then 38 else 43))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 18 else 69) else (if i.val < 131 then 70 else 73)) else (if i.val < 134 then (if i.val < 133 then 74 else 74) else (if i.val < 135 then 69 else 21))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 38 else 22) else (if i.val < 139 then 43 else 69)) else (if i.val < 142 then (if i.val < 141 then 43 else 74) else (if i.val < 143 then 40 else 78)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 71 else 38) else (if i.val < 147 then 21 else 75)) else (if i.val < 150 then (if i.val < 149 then 71 else 74) else (if i.val < 151 then 41 else 21))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 41 else 6) else (if i.val < 155 then 43 else 73)) else (if i.val < 158 then (if i.val < 157 then 43 else 20) else (if i.val < 159 then 72 else 22))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 69 else 73) else (if i.val < 163 then 69 else 72)) else (if i.val < 166 then (if i.val < 165 then 68 else 40) else (if i.val < 167 then 69 else 72))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 94 else 73) else (if i.val < 171 then 70 else 43)) else (if i.val < 174 then (if i.val < 173 then 78 else 69) else (if i.val < 175 then 21 else 69)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 94 else 38) else (if i.val < 179 then 38 else 42)) else (if i.val < 182 then (if i.val < 181 then 77 else 72) else (if i.val < 183 then 38 else 73))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 74 else 38) else (if i.val < 187 then 73 else 70)) else (if i.val < 190 then (if i.val < 189 then 72 else 41) else (if i.val < 191 then 41 else 73)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 73 else 74) else (if i.val < 195 then 74 else 38)) else (if i.val < 198 then (if i.val < 197 then 72 else 18) else (if i.val < 199 then 94 else 68))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 74 else 42) else (if i.val < 203 then 73 else 21)) else (if i.val < 206 then (if i.val < 205 then 38 else 40) else (if i.val < 207 then 71 else 38)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 75 else 73) else (if i.val < 211 then 75 else 73)) else (if i.val < 214 then (if i.val < 213 then 69 else 78) else (if i.val < 215 then 74 else 73))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 75 else 38) else (if i.val < 219 then 79 else 69)) else (if i.val < 222 then (if i.val < 221 then 22 else 75) else (if i.val < 223 then 38 else 73))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 74 else 68) else (if i.val < 227 then 73 else 73)) else (if i.val < 230 then (if i.val < 229 then 79 else 74) else (if i.val < 231 then 73 else 69))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 79 else 75) else (if i.val < 235 then 74 else 74)) else (if i.val < 238 then (if i.val < 237 then 68 else 38) else (if i.val < 239 then 20 else 38)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 18 else 22) else (if i.val < 243 then 21 else 38)) else (if i.val < 246 then (if i.val < 245 then 72 else 71) else (if i.val < 247 then 73 else 42))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 22 else 38) else (if i.val < 251 then 74 else 71)) else (if i.val < 254 then (if i.val < 253 then 71 else 43) else (if i.val < 255 then 40 else 75))))))))

theorem g32p_supplierForest_actual_053 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_053 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_053 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_131959
  · exact g32p_supplierForest_actual_131970
  · exact g32p_supplierForest_actual_131988
  · exact g32p_supplierForest_actual_131989
  · exact g32p_supplierForest_actual_132009
  · exact g32p_supplierForest_actual_132022
  · exact g32p_supplierForest_actual_132036
  · exact g32p_supplierForest_actual_132053
  · exact g32p_supplierForest_actual_132055
  · exact g32p_supplierForest_actual_132112
  · exact g32p_supplierForest_actual_132115
  · exact g32p_supplierForest_actual_132121
  · exact g32p_supplierForest_actual_132144
  · exact g32p_supplierForest_actual_132196
  · exact g32p_supplierForest_actual_132212
  · exact g32p_supplierForest_actual_132214
  · exact g32p_supplierForest_actual_132230
  · exact g32p_supplierForest_actual_132243
  · exact g32p_supplierForest_actual_132280
  · exact g32p_supplierForest_actual_132302
  · exact g32p_supplierForest_actual_132358
  · exact g32p_supplierForest_actual_132376
  · exact g32p_supplierForest_actual_132383
  · exact g32p_supplierForest_actual_132412
  · exact g32p_supplierForest_actual_132452
  · exact g32p_supplierForest_actual_132482
  · exact g32p_supplierForest_actual_132491
  · exact g32p_supplierForest_actual_132514
  · exact g32p_supplierForest_actual_132569
  · exact g32p_supplierForest_actual_132583
  · exact g32p_supplierForest_actual_132639
  · exact g32p_supplierForest_actual_132647
  · exact g32p_supplierForest_actual_132655
  · exact g32p_supplierForest_actual_132719
  · exact g32p_supplierForest_actual_132741
  · exact g32p_supplierForest_actual_132772
  · exact g32p_supplierForest_actual_132778
  · exact g32p_supplierForest_actual_132807
  · exact g32p_supplierForest_actual_132888
  · exact g32p_supplierForest_actual_132897
  · exact g32p_supplierForest_actual_132905
  · exact g32p_supplierForest_actual_132908
  · exact g32p_supplierForest_actual_132992
  · exact g32p_supplierForest_actual_133021
  · exact g32p_supplierForest_actual_133041
  · exact g32p_supplierForest_actual_133107
  · exact g32p_supplierForest_actual_133131
  · exact g32p_supplierForest_actual_133145
  · exact g32p_supplierForest_actual_133146
  · exact g32p_supplierForest_actual_133186
  · exact g32p_supplierForest_actual_133215
  · exact g32p_supplierForest_actual_133217
  · exact g32p_supplierForest_actual_133226
  · exact g32p_supplierForest_actual_133291
  · exact g32p_supplierForest_actual_133334
  · exact g32p_supplierForest_actual_133365
  · exact g32p_supplierForest_actual_133396
  · exact g32p_supplierForest_actual_133405
  · exact g32p_supplierForest_actual_133439
  · exact g32p_supplierForest_actual_133466
  · exact g32p_supplierForest_actual_133506
  · exact g32p_supplierForest_actual_133519
  · exact g32p_supplierForest_actual_133522
  · exact g32p_supplierForest_actual_133537
  · exact g32p_supplierForest_actual_133558
  · exact g32p_supplierForest_actual_133560
  · exact g32p_supplierForest_actual_133575
  · exact g32p_supplierForest_actual_133576
  · exact g32p_supplierForest_actual_133588
  · exact g32p_supplierForest_actual_133647
  · exact g32p_supplierForest_actual_133694
  · exact g32p_supplierForest_actual_133714
  · exact g32p_supplierForest_actual_133729
  · exact g32p_supplierForest_actual_133749
  · exact g32p_supplierForest_actual_133770
  · exact g32p_supplierForest_actual_133782
  · exact g32p_supplierForest_actual_133783
  · exact g32p_supplierForest_actual_133812
  · exact g32p_supplierForest_actual_133820
  · exact g32p_supplierForest_actual_133822
  · exact g32p_supplierForest_actual_133824
  · exact g32p_supplierForest_actual_133826
  · exact g32p_supplierForest_actual_133836
  · exact g32p_supplierForest_actual_133895
  · exact g32p_supplierForest_actual_134015
  · exact g32p_supplierForest_actual_134027
  · exact g32p_supplierForest_actual_134037
  · exact g32p_supplierForest_actual_134072
  · exact g32p_supplierForest_actual_134079
  · exact g32p_supplierForest_actual_134139
  · exact g32p_supplierForest_actual_134141
  · exact g32p_supplierForest_actual_134162
  · exact g32p_supplierForest_actual_134165
  · exact g32p_supplierForest_actual_134201
  · exact g32p_supplierForest_actual_134252
  · exact g32p_supplierForest_actual_134260
  · exact g32p_supplierForest_actual_134287
  · exact g32p_supplierForest_actual_134349
  · exact g32p_supplierForest_actual_134397
  · exact g32p_supplierForest_actual_134423
  · exact g32p_supplierForest_actual_134440
  · exact g32p_supplierForest_actual_134456
  · exact g32p_supplierForest_actual_134557
  · exact g32p_supplierForest_actual_134639
  · exact g32p_supplierForest_actual_134640
  · exact g32p_supplierForest_actual_134689
  · exact g32p_supplierForest_actual_134691
  · exact g32p_supplierForest_actual_134704
  · exact g32p_supplierForest_actual_134746
  · exact g32p_supplierForest_actual_134782
  · exact g32p_supplierForest_actual_134795
  · exact g32p_supplierForest_actual_134845
  · exact g32p_supplierForest_actual_134854
  · exact g32p_supplierForest_actual_134916
  · exact g32p_supplierForest_actual_134931
  · exact g32p_supplierForest_actual_134934
  · exact g32p_supplierForest_actual_134936
  · exact g32p_supplierForest_actual_134942
  · exact g32p_supplierForest_actual_134973
  · exact g32p_supplierForest_actual_134991
  · exact g32p_supplierForest_actual_134993
  · exact g32p_supplierForest_actual_134999
  · exact g32p_supplierForest_actual_135034
  · exact g32p_supplierForest_actual_135109
  · exact g32p_supplierForest_actual_135121
  · exact g32p_supplierForest_actual_135124
  · exact g32p_supplierForest_actual_135130
  · exact g32p_supplierForest_actual_135171
  · exact g32p_supplierForest_actual_135196
  · exact g32p_supplierForest_actual_135206
  · exact g32p_supplierForest_actual_135218
  · exact g32p_supplierForest_actual_135255
  · exact g32p_supplierForest_actual_135365
  · exact g32p_supplierForest_actual_135392
  · exact g32p_supplierForest_actual_135395
  · exact g32p_supplierForest_actual_135488
  · exact g32p_supplierForest_actual_135501
  · exact g32p_supplierForest_actual_135516
  · exact g32p_supplierForest_actual_135557
  · exact g32p_supplierForest_actual_135558
  · exact g32p_supplierForest_actual_135572
  · exact g32p_supplierForest_actual_135578
  · exact g32p_supplierForest_actual_135609
  · exact g32p_supplierForest_actual_135662
  · exact g32p_supplierForest_actual_135679
  · exact g32p_supplierForest_actual_135697
  · exact g32p_supplierForest_actual_135788
  · exact g32p_supplierForest_actual_135812
  · exact g32p_supplierForest_actual_135831
  · exact g32p_supplierForest_actual_135849
  · exact g32p_supplierForest_actual_135868
  · exact g32p_supplierForest_actual_135889
  · exact g32p_supplierForest_actual_135897
  · exact g32p_supplierForest_actual_135912
  · exact g32p_supplierForest_actual_135921
  · exact g32p_supplierForest_actual_135927
  · exact g32p_supplierForest_actual_135984
  · exact g32p_supplierForest_actual_135992
  · exact g32p_supplierForest_actual_136002
  · exact g32p_supplierForest_actual_136038
  · exact g32p_supplierForest_actual_136166
  · exact g32p_supplierForest_actual_136310
  · exact g32p_supplierForest_actual_136353
  · exact g32p_supplierForest_actual_136373
  · exact g32p_supplierForest_actual_136445
  · exact g32p_supplierForest_actual_136447
  · exact g32p_supplierForest_actual_136456
  · exact g32p_supplierForest_actual_136466
  · exact g32p_supplierForest_actual_136471
  · exact g32p_supplierForest_actual_136484
  · exact g32p_supplierForest_actual_136652
  · exact g32p_supplierForest_actual_136660
  · exact g32p_supplierForest_actual_136677
  · exact g32p_supplierForest_actual_136700
  · exact g32p_supplierForest_actual_136757
  · exact g32p_supplierForest_actual_136759
  · exact g32p_supplierForest_actual_136794
  · exact g32p_supplierForest_actual_136811
  · exact g32p_supplierForest_actual_136873
  · exact g32p_supplierForest_actual_136889
  · exact g32p_supplierForest_actual_136933
  · exact g32p_supplierForest_actual_136959
  · exact g32p_supplierForest_actual_136960
  · exact g32p_supplierForest_actual_136971
  · exact g32p_supplierForest_actual_136985
  · exact g32p_supplierForest_actual_137005
  · exact g32p_supplierForest_actual_137032
  · exact g32p_supplierForest_actual_137046
  · exact g32p_supplierForest_actual_137149
  · exact g32p_supplierForest_actual_137167
  · exact g32p_supplierForest_actual_137169
  · exact g32p_supplierForest_actual_137192
  · exact g32p_supplierForest_actual_137199
  · exact g32p_supplierForest_actual_137221
  · exact g32p_supplierForest_actual_137223
  · exact g32p_supplierForest_actual_137237
  · exact g32p_supplierForest_actual_137249
  · exact g32p_supplierForest_actual_137271
  · exact g32p_supplierForest_actual_137286
  · exact g32p_supplierForest_actual_137293
  · exact g32p_supplierForest_actual_137296
  · exact g32p_supplierForest_actual_137323
  · exact g32p_supplierForest_actual_137367
  · exact g32p_supplierForest_actual_137422
  · exact g32p_supplierForest_actual_137502
  · exact g32p_supplierForest_actual_137514
  · exact g32p_supplierForest_actual_137572
  · exact g32p_supplierForest_actual_137689
  · exact g32p_supplierForest_actual_137702
  · exact g32p_supplierForest_actual_137715
  · exact g32p_supplierForest_actual_137739
  · exact g32p_supplierForest_actual_137744
  · exact g32p_supplierForest_actual_137778
  · exact g32p_supplierForest_actual_137801
  · exact g32p_supplierForest_actual_137838
  · exact g32p_supplierForest_actual_137861
  · exact g32p_supplierForest_actual_137879
  · exact g32p_supplierForest_actual_137906
  · exact g32p_supplierForest_actual_137943
  · exact g32p_supplierForest_actual_137954
  · exact g32p_supplierForest_actual_137964
  · exact g32p_supplierForest_actual_137980
  · exact g32p_supplierForest_actual_138002
  · exact g32p_supplierForest_actual_138015
  · exact g32p_supplierForest_actual_138045
  · exact g32p_supplierForest_actual_138076
  · exact g32p_supplierForest_actual_138083
  · exact g32p_supplierForest_actual_138123
  · exact g32p_supplierForest_actual_138134
  · exact g32p_supplierForest_actual_138167
  · exact g32p_supplierForest_actual_138193
  · exact g32p_supplierForest_actual_138204
  · exact g32p_supplierForest_actual_138299
  · exact g32p_supplierForest_actual_138345
  · exact g32p_supplierForest_actual_138425
  · exact g32p_supplierForest_actual_138426
  · exact g32p_supplierForest_actual_138432
  · exact g32p_supplierForest_actual_138442
  · exact g32p_supplierForest_actual_138445
  · exact g32p_supplierForest_actual_138579
  · exact g32p_supplierForest_actual_138636
  · exact g32p_supplierForest_actual_138654
  · exact g32p_supplierForest_actual_138659
  · exact g32p_supplierForest_actual_138660
  · exact g32p_supplierForest_actual_138679
  · exact g32p_supplierForest_actual_138685
  · exact g32p_supplierForest_actual_138701
  · exact g32p_supplierForest_actual_138710
  · exact g32p_supplierForest_actual_138719
  · exact g32p_supplierForest_actual_138767
  · exact g32p_supplierForest_actual_138808
  · exact g32p_supplierForest_actual_138844
  · exact g32p_supplierForest_actual_138887
  · exact g32p_supplierForest_actual_138905
  · exact g32p_supplierForest_actual_138941
  · exact g32p_supplierForest_actual_138969

def g32p_supplierForest_nodes_054 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_138986 else g32p_supplierForest_node_139010) else (if i.val < 3 then g32p_supplierForest_node_139036 else g32p_supplierForest_node_139039)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_139074 else g32p_supplierForest_node_139076) else (if i.val < 7 then g32p_supplierForest_node_139104 else g32p_supplierForest_node_139136))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_139147 else g32p_supplierForest_node_139159) else (if i.val < 11 then g32p_supplierForest_node_139169 else g32p_supplierForest_node_139177)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_139180 else g32p_supplierForest_node_139235) else (if i.val < 15 then g32p_supplierForest_node_139288 else g32p_supplierForest_node_139302)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_139322 else g32p_supplierForest_node_139329) else (if i.val < 19 then g32p_supplierForest_node_139382 else g32p_supplierForest_node_139386)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_139387 else g32p_supplierForest_node_139403) else (if i.val < 23 then g32p_supplierForest_node_139412 else g32p_supplierForest_node_139452))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_139516 else g32p_supplierForest_node_139520) else (if i.val < 27 then g32p_supplierForest_node_139539 else g32p_supplierForest_node_139554)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_139563 else g32p_supplierForest_node_139578) else (if i.val < 31 then g32p_supplierForest_node_139597 else g32p_supplierForest_node_139604))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_139622 else g32p_supplierForest_node_139644) else (if i.val < 35 then g32p_supplierForest_node_139653 else g32p_supplierForest_node_139716)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_139717 else g32p_supplierForest_node_139752) else (if i.val < 39 then g32p_supplierForest_node_139761 else g32p_supplierForest_node_139765))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_139783 else g32p_supplierForest_node_139794) else (if i.val < 43 then g32p_supplierForest_node_139812 else g32p_supplierForest_node_139816)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_139830 else g32p_supplierForest_node_139854) else (if i.val < 47 then g32p_supplierForest_node_139863 else g32p_supplierForest_node_139879)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_139918 else g32p_supplierForest_node_139954) else (if i.val < 51 then g32p_supplierForest_node_139984 else g32p_supplierForest_node_139993)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_140033 else g32p_supplierForest_node_140056) else (if i.val < 55 then g32p_supplierForest_node_140082 else g32p_supplierForest_node_140105))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_140194 else g32p_supplierForest_node_140220) else (if i.val < 59 then g32p_supplierForest_node_140238 else g32p_supplierForest_node_140260)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_140261 else g32p_supplierForest_node_140266) else (if i.val < 63 then g32p_supplierForest_node_140269 else g32p_supplierForest_node_140279)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_140336 else g32p_supplierForest_node_140355) else (if i.val < 67 then g32p_supplierForest_node_140416 else g32p_supplierForest_node_140439)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_140443 else g32p_supplierForest_node_140451) else (if i.val < 71 then g32p_supplierForest_node_140485 else g32p_supplierForest_node_140489))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_140490 else g32p_supplierForest_node_140519) else (if i.val < 75 then g32p_supplierForest_node_140521 else g32p_supplierForest_node_140552)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_140588 else g32p_supplierForest_node_140597) else (if i.val < 79 then g32p_supplierForest_node_140628 else g32p_supplierForest_node_140672)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_140834 else g32p_supplierForest_node_140835) else (if i.val < 83 then g32p_supplierForest_node_140892 else g32p_supplierForest_node_140934)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_140997 else g32p_supplierForest_node_141004) else (if i.val < 87 then g32p_supplierForest_node_141014 else g32p_supplierForest_node_141115))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_141151 else g32p_supplierForest_node_141175) else (if i.val < 91 then g32p_supplierForest_node_141181 else g32p_supplierForest_node_141183)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_141198 else g32p_supplierForest_node_141230) else (if i.val < 95 then g32p_supplierForest_node_141245 else g32p_supplierForest_node_141256))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_141257 else g32p_supplierForest_node_141267) else (if i.val < 99 then g32p_supplierForest_node_141294 else g32p_supplierForest_node_141295)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_141298 else g32p_supplierForest_node_141341) else (if i.val < 103 then g32p_supplierForest_node_141348 else g32p_supplierForest_node_141385))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_141416 else g32p_supplierForest_node_141427) else (if i.val < 107 then g32p_supplierForest_node_141500 else g32p_supplierForest_node_141502)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_141537 else g32p_supplierForest_node_141597) else (if i.val < 111 then g32p_supplierForest_node_141619 else g32p_supplierForest_node_141622)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_141644 else g32p_supplierForest_node_141660) else (if i.val < 115 then g32p_supplierForest_node_141700 else g32p_supplierForest_node_141719)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_141737 else g32p_supplierForest_node_141760) else (if i.val < 119 then g32p_supplierForest_node_141837 else g32p_supplierForest_node_141879))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_142030 else g32p_supplierForest_node_142032) else (if i.val < 123 then g32p_supplierForest_node_142049 else g32p_supplierForest_node_142058)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_142103 else g32p_supplierForest_node_142111) else (if i.val < 127 then g32p_supplierForest_node_142130 else g32p_supplierForest_node_142134))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_142147 else g32p_supplierForest_node_142173) else (if i.val < 131 then g32p_supplierForest_node_142316 else g32p_supplierForest_node_142319)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_142335 else g32p_supplierForest_node_142341) else (if i.val < 135 then g32p_supplierForest_node_142355 else g32p_supplierForest_node_142373))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_142374 else g32p_supplierForest_node_142398) else (if i.val < 139 then g32p_supplierForest_node_142421 else g32p_supplierForest_node_142437)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_142452 else g32p_supplierForest_node_142468) else (if i.val < 143 then g32p_supplierForest_node_142487 else g32p_supplierForest_node_142517)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_142521 else g32p_supplierForest_node_142544) else (if i.val < 147 then g32p_supplierForest_node_142545 else g32p_supplierForest_node_142551)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_142561 else g32p_supplierForest_node_142600) else (if i.val < 151 then g32p_supplierForest_node_142615 else g32p_supplierForest_node_142637))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_142681 else g32p_supplierForest_node_142742) else (if i.val < 155 then g32p_supplierForest_node_142745 else g32p_supplierForest_node_142762)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_142763 else g32p_supplierForest_node_142781) else (if i.val < 159 then g32p_supplierForest_node_142782 else g32p_supplierForest_node_142803))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_142897 else g32p_supplierForest_node_143041) else (if i.val < 163 then g32p_supplierForest_node_143043 else g32p_supplierForest_node_143126)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_143132 else g32p_supplierForest_node_143141) else (if i.val < 167 then g32p_supplierForest_node_143146 else g32p_supplierForest_node_143198))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_143246 else g32p_supplierForest_node_143272) else (if i.val < 171 then g32p_supplierForest_node_143279 else g32p_supplierForest_node_143295)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_143312 else g32p_supplierForest_node_143332) else (if i.val < 175 then g32p_supplierForest_node_143373 else g32p_supplierForest_node_143412)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_143548 else g32p_supplierForest_node_143553) else (if i.val < 179 then g32p_supplierForest_node_143575 else g32p_supplierForest_node_143583)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_143587 else g32p_supplierForest_node_143612) else (if i.val < 183 then g32p_supplierForest_node_143642 else g32p_supplierForest_node_143666))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_143667 else g32p_supplierForest_node_143698) else (if i.val < 187 then g32p_supplierForest_node_143699 else g32p_supplierForest_node_143776)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_143790 else g32p_supplierForest_node_143858) else (if i.val < 191 then g32p_supplierForest_node_143893 else g32p_supplierForest_node_143904)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_143931 else g32p_supplierForest_node_143937) else (if i.val < 195 then g32p_supplierForest_node_143966 else g32p_supplierForest_node_143996)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_144023 else g32p_supplierForest_node_144060) else (if i.val < 199 then g32p_supplierForest_node_144089 else g32p_supplierForest_node_144111))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_144115 else g32p_supplierForest_node_144198) else (if i.val < 203 then g32p_supplierForest_node_144205 else g32p_supplierForest_node_144249)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_144269 else g32p_supplierForest_node_144365) else (if i.val < 207 then g32p_supplierForest_node_144372 else g32p_supplierForest_node_144375)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_144380 else g32p_supplierForest_node_144439) else (if i.val < 211 then g32p_supplierForest_node_144455 else g32p_supplierForest_node_144468)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_144487 else g32p_supplierForest_node_144494) else (if i.val < 215 then g32p_supplierForest_node_144504 else g32p_supplierForest_node_144515))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_144533 else g32p_supplierForest_node_144534) else (if i.val < 219 then g32p_supplierForest_node_144549 else g32p_supplierForest_node_144566)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_144573 else g32p_supplierForest_node_144581) else (if i.val < 223 then g32p_supplierForest_node_144597 else g32p_supplierForest_node_144598))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_144625 else g32p_supplierForest_node_144628) else (if i.val < 227 then g32p_supplierForest_node_144636 else g32p_supplierForest_node_144638)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_144639 else g32p_supplierForest_node_144645) else (if i.val < 231 then g32p_supplierForest_node_144701 else g32p_supplierForest_node_144705))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_144719 else g32p_supplierForest_node_144747) else (if i.val < 235 then g32p_supplierForest_node_144756 else g32p_supplierForest_node_144769)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_144779 else g32p_supplierForest_node_144795) else (if i.val < 239 then g32p_supplierForest_node_144799 else g32p_supplierForest_node_144800)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_144812 else g32p_supplierForest_node_144819) else (if i.val < 243 then g32p_supplierForest_node_144821 else g32p_supplierForest_node_144829)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_144839 else g32p_supplierForest_node_144860) else (if i.val < 247 then g32p_supplierForest_node_144880 else g32p_supplierForest_node_144922))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_144971 else g32p_supplierForest_node_144999) else (if i.val < 251 then g32p_supplierForest_node_145023 else g32p_supplierForest_node_145032)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_145046 else g32p_supplierForest_node_145047) else (if i.val < 255 then g32p_supplierForest_node_145068 else g32p_supplierForest_node_145087))))))))

def g32p_supplierForest_classes_054 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 94 else 20) else (if i.val < 3 then 94 else 42)) else (if i.val < 6 then (if i.val < 5 then 20 else 73) else (if i.val < 7 then 41 else 38))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 38 else 73) else (if i.val < 11 then 69 else 75)) else (if i.val < 14 then (if i.val < 13 then 73 else 77) else (if i.val < 15 then 43 else 72)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 73 else 73) else (if i.val < 19 then 69 else 74)) else (if i.val < 22 then (if i.val < 21 then 73 else 74) else (if i.val < 23 then 72 else 38))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 40 else 71) else (if i.val < 27 then 73 else 38)) else (if i.val < 30 then (if i.val < 29 then 38 else 20) else (if i.val < 31 then 94 else 72))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 42 else 69) else (if i.val < 35 then 73 else 75)) else (if i.val < 38 then (if i.val < 37 then 75 else 94) else (if i.val < 39 then 94 else 75))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 75 else 75) else (if i.val < 43 then 79 else 71)) else (if i.val < 46 then (if i.val < 45 then 73 else 75) else (if i.val < 47 then 77 else 42)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 38 else 70) else (if i.val < 51 then 73 else 73)) else (if i.val < 54 then (if i.val < 53 then 38 else 74) else (if i.val < 55 then 43 else 74))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 73 else 73) else (if i.val < 59 then 71 else 38)) else (if i.val < 62 then (if i.val < 61 then 70 else 75) else (if i.val < 63 then 73 else 22)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 75 else 94) else (if i.val < 67 then 71 else 77)) else (if i.val < 70 then (if i.val < 69 then 94 else 42) else (if i.val < 71 then 94 else 21))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 74 else 78) else (if i.val < 75 then 71 else 38)) else (if i.val < 78 then (if i.val < 77 then 73 else 38) else (if i.val < 79 then 74 else 94)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 21 else 73) else (if i.val < 83 then 74 else 73)) else (if i.val < 86 then (if i.val < 85 then 73 else 95) else (if i.val < 87 then 71 else 77))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 38 else 78) else (if i.val < 91 then 94 else 41)) else (if i.val < 94 then (if i.val < 93 then 79 else 41) else (if i.val < 95 then 73 else 94))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 73 else 38) else (if i.val < 99 then 41 else 21)) else (if i.val < 102 then (if i.val < 101 then 72 else 71) else (if i.val < 103 then 72 else 72))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 69 else 73) else (if i.val < 107 then 73 else 71)) else (if i.val < 110 then (if i.val < 109 then 71 else 42) else (if i.val < 111 then 73 else 94)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 69 else 78) else (if i.val < 115 then 76 else 38)) else (if i.val < 118 then (if i.val < 117 then 94 else 73) else (if i.val < 119 then 43 else 42))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 71 else 71) else (if i.val < 123 then 21 else 22)) else (if i.val < 126 then (if i.val < 125 then 77 else 69) else (if i.val < 127 then 18 else 78))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 42 else 73) else (if i.val < 131 then 72 else 73)) else (if i.val < 134 then (if i.val < 133 then 18 else 94) else (if i.val < 135 then 21 else 71))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 69 else 71) else (if i.val < 139 then 38 else 94)) else (if i.val < 142 then (if i.val < 141 then 94 else 69) else (if i.val < 143 then 21 else 38)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 71 else 73) else (if i.val < 147 then 72 else 71)) else (if i.val < 150 then (if i.val < 149 then 79 else 38) else (if i.val < 151 then 74 else 77))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 73 else 78) else (if i.val < 155 then 75 else 73)) else (if i.val < 158 then (if i.val < 157 then 78 else 73) else (if i.val < 159 then 70 else 94))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 74 else 77) else (if i.val < 163 then 73 else 42)) else (if i.val < 166 then (if i.val < 165 then 69 else 94) else (if i.val < 167 then 38 else 78))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 94) else (if i.val < 171 then 71 else 20)) else (if i.val < 174 then (if i.val < 173 then 74 else 78) else (if i.val < 175 then 77 else 78)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 73 else 94) else (if i.val < 179 then 78 else 42)) else (if i.val < 182 then (if i.val < 181 then 78 else 73) else (if i.val < 183 then 73 else 73))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 71 else 74) else (if i.val < 187 then 77 else 94)) else (if i.val < 190 then (if i.val < 189 then 73 else 73) else (if i.val < 191 then 71 else 77)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 72 else 72) else (if i.val < 195 then 78 else 78)) else (if i.val < 198 then (if i.val < 197 then 75 else 42) else (if i.val < 199 then 71 else 21))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 73 else 42) else (if i.val < 203 then 42 else 73)) else (if i.val < 206 then (if i.val < 205 then 78 else 73) else (if i.val < 207 then 42 else 78)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 71 else 78) else (if i.val < 211 then 79 else 94)) else (if i.val < 214 then (if i.val < 213 then 78 else 73) else (if i.val < 215 then 71 else 78))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 73 else 78) else (if i.val < 219 then 73 else 71)) else (if i.val < 222 then (if i.val < 221 then 73 else 78) else (if i.val < 223 then 71 else 75))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 84 else 9) else (if i.val < 227 then 53 else 53)) else (if i.val < 230 then (if i.val < 229 then 84 else 49) else (if i.val < 231 then 26 else 86))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 54 else 26) else (if i.val < 235 then 86 else 80)) else (if i.val < 238 then (if i.val < 237 then 80 else 86) else (if i.val < 239 then 86 else 83)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 84 else 84) else (if i.val < 243 then 53 else 55)) else (if i.val < 246 then (if i.val < 245 then 55 else 46) else (if i.val < 247 then 47 else 53))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 46 else 52) else (if i.val < 251 then 55 else 80)) else (if i.val < 254 then (if i.val < 253 then 54 else 86) else (if i.val < 255 then 81 else 45))))))))

theorem g32p_supplierForest_actual_054 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_054 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_054 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_138986
  · exact g32p_supplierForest_actual_139010
  · exact g32p_supplierForest_actual_139036
  · exact g32p_supplierForest_actual_139039
  · exact g32p_supplierForest_actual_139074
  · exact g32p_supplierForest_actual_139076
  · exact g32p_supplierForest_actual_139104
  · exact g32p_supplierForest_actual_139136
  · exact g32p_supplierForest_actual_139147
  · exact g32p_supplierForest_actual_139159
  · exact g32p_supplierForest_actual_139169
  · exact g32p_supplierForest_actual_139177
  · exact g32p_supplierForest_actual_139180
  · exact g32p_supplierForest_actual_139235
  · exact g32p_supplierForest_actual_139288
  · exact g32p_supplierForest_actual_139302
  · exact g32p_supplierForest_actual_139322
  · exact g32p_supplierForest_actual_139329
  · exact g32p_supplierForest_actual_139382
  · exact g32p_supplierForest_actual_139386
  · exact g32p_supplierForest_actual_139387
  · exact g32p_supplierForest_actual_139403
  · exact g32p_supplierForest_actual_139412
  · exact g32p_supplierForest_actual_139452
  · exact g32p_supplierForest_actual_139516
  · exact g32p_supplierForest_actual_139520
  · exact g32p_supplierForest_actual_139539
  · exact g32p_supplierForest_actual_139554
  · exact g32p_supplierForest_actual_139563
  · exact g32p_supplierForest_actual_139578
  · exact g32p_supplierForest_actual_139597
  · exact g32p_supplierForest_actual_139604
  · exact g32p_supplierForest_actual_139622
  · exact g32p_supplierForest_actual_139644
  · exact g32p_supplierForest_actual_139653
  · exact g32p_supplierForest_actual_139716
  · exact g32p_supplierForest_actual_139717
  · exact g32p_supplierForest_actual_139752
  · exact g32p_supplierForest_actual_139761
  · exact g32p_supplierForest_actual_139765
  · exact g32p_supplierForest_actual_139783
  · exact g32p_supplierForest_actual_139794
  · exact g32p_supplierForest_actual_139812
  · exact g32p_supplierForest_actual_139816
  · exact g32p_supplierForest_actual_139830
  · exact g32p_supplierForest_actual_139854
  · exact g32p_supplierForest_actual_139863
  · exact g32p_supplierForest_actual_139879
  · exact g32p_supplierForest_actual_139918
  · exact g32p_supplierForest_actual_139954
  · exact g32p_supplierForest_actual_139984
  · exact g32p_supplierForest_actual_139993
  · exact g32p_supplierForest_actual_140033
  · exact g32p_supplierForest_actual_140056
  · exact g32p_supplierForest_actual_140082
  · exact g32p_supplierForest_actual_140105
  · exact g32p_supplierForest_actual_140194
  · exact g32p_supplierForest_actual_140220
  · exact g32p_supplierForest_actual_140238
  · exact g32p_supplierForest_actual_140260
  · exact g32p_supplierForest_actual_140261
  · exact g32p_supplierForest_actual_140266
  · exact g32p_supplierForest_actual_140269
  · exact g32p_supplierForest_actual_140279
  · exact g32p_supplierForest_actual_140336
  · exact g32p_supplierForest_actual_140355
  · exact g32p_supplierForest_actual_140416
  · exact g32p_supplierForest_actual_140439
  · exact g32p_supplierForest_actual_140443
  · exact g32p_supplierForest_actual_140451
  · exact g32p_supplierForest_actual_140485
  · exact g32p_supplierForest_actual_140489
  · exact g32p_supplierForest_actual_140490
  · exact g32p_supplierForest_actual_140519
  · exact g32p_supplierForest_actual_140521
  · exact g32p_supplierForest_actual_140552
  · exact g32p_supplierForest_actual_140588
  · exact g32p_supplierForest_actual_140597
  · exact g32p_supplierForest_actual_140628
  · exact g32p_supplierForest_actual_140672
  · exact g32p_supplierForest_actual_140834
  · exact g32p_supplierForest_actual_140835
  · exact g32p_supplierForest_actual_140892
  · exact g32p_supplierForest_actual_140934
  · exact g32p_supplierForest_actual_140997
  · exact g32p_supplierForest_actual_141004
  · exact g32p_supplierForest_actual_141014
  · exact g32p_supplierForest_actual_141115
  · exact g32p_supplierForest_actual_141151
  · exact g32p_supplierForest_actual_141175
  · exact g32p_supplierForest_actual_141181
  · exact g32p_supplierForest_actual_141183
  · exact g32p_supplierForest_actual_141198
  · exact g32p_supplierForest_actual_141230
  · exact g32p_supplierForest_actual_141245
  · exact g32p_supplierForest_actual_141256
  · exact g32p_supplierForest_actual_141257
  · exact g32p_supplierForest_actual_141267
  · exact g32p_supplierForest_actual_141294
  · exact g32p_supplierForest_actual_141295
  · exact g32p_supplierForest_actual_141298
  · exact g32p_supplierForest_actual_141341
  · exact g32p_supplierForest_actual_141348
  · exact g32p_supplierForest_actual_141385
  · exact g32p_supplierForest_actual_141416
  · exact g32p_supplierForest_actual_141427
  · exact g32p_supplierForest_actual_141500
  · exact g32p_supplierForest_actual_141502
  · exact g32p_supplierForest_actual_141537
  · exact g32p_supplierForest_actual_141597
  · exact g32p_supplierForest_actual_141619
  · exact g32p_supplierForest_actual_141622
  · exact g32p_supplierForest_actual_141644
  · exact g32p_supplierForest_actual_141660
  · exact g32p_supplierForest_actual_141700
  · exact g32p_supplierForest_actual_141719
  · exact g32p_supplierForest_actual_141737
  · exact g32p_supplierForest_actual_141760
  · exact g32p_supplierForest_actual_141837
  · exact g32p_supplierForest_actual_141879
  · exact g32p_supplierForest_actual_142030
  · exact g32p_supplierForest_actual_142032
  · exact g32p_supplierForest_actual_142049
  · exact g32p_supplierForest_actual_142058
  · exact g32p_supplierForest_actual_142103
  · exact g32p_supplierForest_actual_142111
  · exact g32p_supplierForest_actual_142130
  · exact g32p_supplierForest_actual_142134
  · exact g32p_supplierForest_actual_142147
  · exact g32p_supplierForest_actual_142173
  · exact g32p_supplierForest_actual_142316
  · exact g32p_supplierForest_actual_142319
  · exact g32p_supplierForest_actual_142335
  · exact g32p_supplierForest_actual_142341
  · exact g32p_supplierForest_actual_142355
  · exact g32p_supplierForest_actual_142373
  · exact g32p_supplierForest_actual_142374
  · exact g32p_supplierForest_actual_142398
  · exact g32p_supplierForest_actual_142421
  · exact g32p_supplierForest_actual_142437
  · exact g32p_supplierForest_actual_142452
  · exact g32p_supplierForest_actual_142468
  · exact g32p_supplierForest_actual_142487
  · exact g32p_supplierForest_actual_142517
  · exact g32p_supplierForest_actual_142521
  · exact g32p_supplierForest_actual_142544
  · exact g32p_supplierForest_actual_142545
  · exact g32p_supplierForest_actual_142551
  · exact g32p_supplierForest_actual_142561
  · exact g32p_supplierForest_actual_142600
  · exact g32p_supplierForest_actual_142615
  · exact g32p_supplierForest_actual_142637
  · exact g32p_supplierForest_actual_142681
  · exact g32p_supplierForest_actual_142742
  · exact g32p_supplierForest_actual_142745
  · exact g32p_supplierForest_actual_142762
  · exact g32p_supplierForest_actual_142763
  · exact g32p_supplierForest_actual_142781
  · exact g32p_supplierForest_actual_142782
  · exact g32p_supplierForest_actual_142803
  · exact g32p_supplierForest_actual_142897
  · exact g32p_supplierForest_actual_143041
  · exact g32p_supplierForest_actual_143043
  · exact g32p_supplierForest_actual_143126
  · exact g32p_supplierForest_actual_143132
  · exact g32p_supplierForest_actual_143141
  · exact g32p_supplierForest_actual_143146
  · exact g32p_supplierForest_actual_143198
  · exact g32p_supplierForest_actual_143246
  · exact g32p_supplierForest_actual_143272
  · exact g32p_supplierForest_actual_143279
  · exact g32p_supplierForest_actual_143295
  · exact g32p_supplierForest_actual_143312
  · exact g32p_supplierForest_actual_143332
  · exact g32p_supplierForest_actual_143373
  · exact g32p_supplierForest_actual_143412
  · exact g32p_supplierForest_actual_143548
  · exact g32p_supplierForest_actual_143553
  · exact g32p_supplierForest_actual_143575
  · exact g32p_supplierForest_actual_143583
  · exact g32p_supplierForest_actual_143587
  · exact g32p_supplierForest_actual_143612
  · exact g32p_supplierForest_actual_143642
  · exact g32p_supplierForest_actual_143666
  · exact g32p_supplierForest_actual_143667
  · exact g32p_supplierForest_actual_143698
  · exact g32p_supplierForest_actual_143699
  · exact g32p_supplierForest_actual_143776
  · exact g32p_supplierForest_actual_143790
  · exact g32p_supplierForest_actual_143858
  · exact g32p_supplierForest_actual_143893
  · exact g32p_supplierForest_actual_143904
  · exact g32p_supplierForest_actual_143931
  · exact g32p_supplierForest_actual_143937
  · exact g32p_supplierForest_actual_143966
  · exact g32p_supplierForest_actual_143996
  · exact g32p_supplierForest_actual_144023
  · exact g32p_supplierForest_actual_144060
  · exact g32p_supplierForest_actual_144089
  · exact g32p_supplierForest_actual_144111
  · exact g32p_supplierForest_actual_144115
  · exact g32p_supplierForest_actual_144198
  · exact g32p_supplierForest_actual_144205
  · exact g32p_supplierForest_actual_144249
  · exact g32p_supplierForest_actual_144269
  · exact g32p_supplierForest_actual_144365
  · exact g32p_supplierForest_actual_144372
  · exact g32p_supplierForest_actual_144375
  · exact g32p_supplierForest_actual_144380
  · exact g32p_supplierForest_actual_144439
  · exact g32p_supplierForest_actual_144455
  · exact g32p_supplierForest_actual_144468
  · exact g32p_supplierForest_actual_144487
  · exact g32p_supplierForest_actual_144494
  · exact g32p_supplierForest_actual_144504
  · exact g32p_supplierForest_actual_144515
  · exact g32p_supplierForest_actual_144533
  · exact g32p_supplierForest_actual_144534
  · exact g32p_supplierForest_actual_144549
  · exact g32p_supplierForest_actual_144566
  · exact g32p_supplierForest_actual_144573
  · exact g32p_supplierForest_actual_144581
  · exact g32p_supplierForest_actual_144597
  · exact g32p_supplierForest_actual_144598
  · exact g32p_supplierForest_actual_144625
  · exact g32p_supplierForest_actual_144628
  · exact g32p_supplierForest_actual_144636
  · exact g32p_supplierForest_actual_144638
  · exact g32p_supplierForest_actual_144639
  · exact g32p_supplierForest_actual_144645
  · exact g32p_supplierForest_actual_144701
  · exact g32p_supplierForest_actual_144705
  · exact g32p_supplierForest_actual_144719
  · exact g32p_supplierForest_actual_144747
  · exact g32p_supplierForest_actual_144756
  · exact g32p_supplierForest_actual_144769
  · exact g32p_supplierForest_actual_144779
  · exact g32p_supplierForest_actual_144795
  · exact g32p_supplierForest_actual_144799
  · exact g32p_supplierForest_actual_144800
  · exact g32p_supplierForest_actual_144812
  · exact g32p_supplierForest_actual_144819
  · exact g32p_supplierForest_actual_144821
  · exact g32p_supplierForest_actual_144829
  · exact g32p_supplierForest_actual_144839
  · exact g32p_supplierForest_actual_144860
  · exact g32p_supplierForest_actual_144880
  · exact g32p_supplierForest_actual_144922
  · exact g32p_supplierForest_actual_144971
  · exact g32p_supplierForest_actual_144999
  · exact g32p_supplierForest_actual_145023
  · exact g32p_supplierForest_actual_145032
  · exact g32p_supplierForest_actual_145046
  · exact g32p_supplierForest_actual_145047
  · exact g32p_supplierForest_actual_145068
  · exact g32p_supplierForest_actual_145087

def g32p_supplierForest_nodes_055 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_145178 else g32p_supplierForest_node_145179) else (if i.val < 3 then g32p_supplierForest_node_145203 else g32p_supplierForest_node_145210)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_145226 else g32p_supplierForest_node_145261) else (if i.val < 7 then g32p_supplierForest_node_145287 else g32p_supplierForest_node_145311))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_145345 else g32p_supplierForest_node_145406) else (if i.val < 11 then g32p_supplierForest_node_145411 else g32p_supplierForest_node_145443)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_145451 else g32p_supplierForest_node_145460) else (if i.val < 15 then g32p_supplierForest_node_145484 else g32p_supplierForest_node_145575)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_145589 else g32p_supplierForest_node_145617) else (if i.val < 19 then g32p_supplierForest_node_145621 else g32p_supplierForest_node_145642)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_145681 else g32p_supplierForest_node_145705) else (if i.val < 23 then g32p_supplierForest_node_145721 else g32p_supplierForest_node_145736))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_145770 else g32p_supplierForest_node_145778) else (if i.val < 27 then g32p_supplierForest_node_145786 else g32p_supplierForest_node_145820)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_145832 else g32p_supplierForest_node_145859) else (if i.val < 31 then g32p_supplierForest_node_145912 else g32p_supplierForest_node_145934))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_145967 else g32p_supplierForest_node_145986) else (if i.val < 35 then g32p_supplierForest_node_146002 else g32p_supplierForest_node_146018)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_146023 else g32p_supplierForest_node_146066) else (if i.val < 39 then g32p_supplierForest_node_146099 else g32p_supplierForest_node_146109))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_146151 else g32p_supplierForest_node_146154) else (if i.val < 43 then g32p_supplierForest_node_146181 else g32p_supplierForest_node_146198)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_146202 else g32p_supplierForest_node_146218) else (if i.val < 47 then g32p_supplierForest_node_146238 else g32p_supplierForest_node_146264)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_146315 else g32p_supplierForest_node_146328) else (if i.val < 51 then g32p_supplierForest_node_146359 else g32p_supplierForest_node_146361)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_146403 else g32p_supplierForest_node_146418) else (if i.val < 55 then g32p_supplierForest_node_146431 else g32p_supplierForest_node_146499))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_146505 else g32p_supplierForest_node_146519) else (if i.val < 59 then g32p_supplierForest_node_146526 else g32p_supplierForest_node_146527)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_146576 else g32p_supplierForest_node_146620) else (if i.val < 63 then g32p_supplierForest_node_146639 else g32p_supplierForest_node_146650)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_146744 else g32p_supplierForest_node_146750) else (if i.val < 67 then g32p_supplierForest_node_146788 else g32p_supplierForest_node_146794)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_146811 else g32p_supplierForest_node_146820) else (if i.val < 71 then g32p_supplierForest_node_146827 else g32p_supplierForest_node_146829))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_146836 else g32p_supplierForest_node_146853) else (if i.val < 75 then g32p_supplierForest_node_146857 else g32p_supplierForest_node_146869)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_146881 else g32p_supplierForest_node_146896) else (if i.val < 79 then g32p_supplierForest_node_146957 else g32p_supplierForest_node_146963)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_146978 else g32p_supplierForest_node_146994) else (if i.val < 83 then g32p_supplierForest_node_147010 else g32p_supplierForest_node_147016)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_147052 else g32p_supplierForest_node_147055) else (if i.val < 87 then g32p_supplierForest_node_147056 else g32p_supplierForest_node_147062))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_147105 else g32p_supplierForest_node_147191) else (if i.val < 91 then g32p_supplierForest_node_147248 else g32p_supplierForest_node_147289)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_147300 else g32p_supplierForest_node_147301) else (if i.val < 95 then g32p_supplierForest_node_147336 else g32p_supplierForest_node_147342))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_147370 else g32p_supplierForest_node_147430) else (if i.val < 99 then g32p_supplierForest_node_147441 else g32p_supplierForest_node_147459)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_147464 else g32p_supplierForest_node_147475) else (if i.val < 103 then g32p_supplierForest_node_147508 else g32p_supplierForest_node_147527))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_147583 else g32p_supplierForest_node_147632) else (if i.val < 107 then g32p_supplierForest_node_147749 else g32p_supplierForest_node_147780)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_147786 else g32p_supplierForest_node_147790) else (if i.val < 111 then g32p_supplierForest_node_147792 else g32p_supplierForest_node_147873)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_147878 else g32p_supplierForest_node_147907) else (if i.val < 115 then g32p_supplierForest_node_147954 else g32p_supplierForest_node_147973)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_147984 else g32p_supplierForest_node_148006) else (if i.val < 119 then g32p_supplierForest_node_148008 else g32p_supplierForest_node_148044))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_148113 else g32p_supplierForest_node_148115) else (if i.val < 123 then g32p_supplierForest_node_148129 else g32p_supplierForest_node_148183)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_148191 else g32p_supplierForest_node_148195) else (if i.val < 127 then g32p_supplierForest_node_148264 else g32p_supplierForest_node_148273))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_148299 else g32p_supplierForest_node_148340) else (if i.val < 131 then g32p_supplierForest_node_148404 else g32p_supplierForest_node_148429)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_148451 else g32p_supplierForest_node_148453) else (if i.val < 135 then g32p_supplierForest_node_148461 else g32p_supplierForest_node_148467))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_148487 else g32p_supplierForest_node_148567) else (if i.val < 139 then g32p_supplierForest_node_148618 else g32p_supplierForest_node_148690)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_148691 else g32p_supplierForest_node_148701) else (if i.val < 143 then g32p_supplierForest_node_148754 else g32p_supplierForest_node_148770)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_148786 else g32p_supplierForest_node_148823) else (if i.val < 147 then g32p_supplierForest_node_148839 else g32p_supplierForest_node_148845)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_148865 else g32p_supplierForest_node_148903) else (if i.val < 151 then g32p_supplierForest_node_148909 else g32p_supplierForest_node_148912))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_148913 else g32p_supplierForest_node_148994) else (if i.val < 155 then g32p_supplierForest_node_149029 else g32p_supplierForest_node_149045)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_149077 else g32p_supplierForest_node_149131) else (if i.val < 159 then g32p_supplierForest_node_149138 else g32p_supplierForest_node_149175))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_149178 else g32p_supplierForest_node_149188) else (if i.val < 163 then g32p_supplierForest_node_149224 else g32p_supplierForest_node_149255)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_149307 else g32p_supplierForest_node_149328) else (if i.val < 167 then g32p_supplierForest_node_149333 else g32p_supplierForest_node_149355))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_149357 else g32p_supplierForest_node_149367) else (if i.val < 171 then g32p_supplierForest_node_149381 else g32p_supplierForest_node_149416)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_149434 else g32p_supplierForest_node_149465) else (if i.val < 175 then g32p_supplierForest_node_149473 else g32p_supplierForest_node_149490)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_149555 else g32p_supplierForest_node_149632) else (if i.val < 179 then g32p_supplierForest_node_149633 else g32p_supplierForest_node_149766)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_149803 else g32p_supplierForest_node_149829) else (if i.val < 183 then g32p_supplierForest_node_149830 else g32p_supplierForest_node_149845))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_149885 else g32p_supplierForest_node_149892) else (if i.val < 187 then g32p_supplierForest_node_149902 else g32p_supplierForest_node_149909)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_149985 else g32p_supplierForest_node_149992) else (if i.val < 191 then g32p_supplierForest_node_150117 else g32p_supplierForest_node_150162)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_150177 else g32p_supplierForest_node_150187) else (if i.val < 195 then g32p_supplierForest_node_150196 else g32p_supplierForest_node_150198)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_150265 else g32p_supplierForest_node_150282) else (if i.val < 199 then g32p_supplierForest_node_150313 else g32p_supplierForest_node_150329))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_150366 else g32p_supplierForest_node_150386) else (if i.val < 203 then g32p_supplierForest_node_150464 else g32p_supplierForest_node_150493)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_150502 else g32p_supplierForest_node_150537) else (if i.val < 207 then g32p_supplierForest_node_150552 else g32p_supplierForest_node_150676)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_150689 else g32p_supplierForest_node_150700) else (if i.val < 211 then g32p_supplierForest_node_150724 else g32p_supplierForest_node_150761)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_150787 else g32p_supplierForest_node_150834) else (if i.val < 215 then g32p_supplierForest_node_150902 else g32p_supplierForest_node_151034))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_151055 else g32p_supplierForest_node_151097) else (if i.val < 219 then g32p_supplierForest_node_151204 else g32p_supplierForest_node_151209)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_151246 else g32p_supplierForest_node_151253) else (if i.val < 223 then g32p_supplierForest_node_151286 else g32p_supplierForest_node_151333))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_151386 else g32p_supplierForest_node_151403) else (if i.val < 227 then g32p_supplierForest_node_151431 else g32p_supplierForest_node_151441)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_151574 else g32p_supplierForest_node_151588) else (if i.val < 231 then g32p_supplierForest_node_151608 else g32p_supplierForest_node_151651))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_151670 else g32p_supplierForest_node_151680) else (if i.val < 235 then g32p_supplierForest_node_151682 else g32p_supplierForest_node_151686)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_151701 else g32p_supplierForest_node_151724) else (if i.val < 239 then g32p_supplierForest_node_151751 else g32p_supplierForest_node_151754)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_151785 else g32p_supplierForest_node_151803) else (if i.val < 243 then g32p_supplierForest_node_151815 else g32p_supplierForest_node_151823)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_151840 else g32p_supplierForest_node_151862) else (if i.val < 247 then g32p_supplierForest_node_151901 else g32p_supplierForest_node_151978))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_152007 else g32p_supplierForest_node_152015) else (if i.val < 251 then g32p_supplierForest_node_152019 else g32p_supplierForest_node_152208)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_152211 else g32p_supplierForest_node_152218) else (if i.val < 255 then g32p_supplierForest_node_152257 else g32p_supplierForest_node_152298))))))))

def g32p_supplierForest_classes_055 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 86 else 81) else (if i.val < 3 then 54 else 86)) else (if i.val < 6 then (if i.val < 5 then 86 else 55) else (if i.val < 7 then 49 else 84))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 86 else 86) else (if i.val < 11 then 81 else 54)) else (if i.val < 14 then (if i.val < 13 then 86 else 86) else (if i.val < 15 then 86 else 45)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 50 else 11) else (if i.val < 19 then 49 else 25)) else (if i.val < 22 then (if i.val < 21 then 55 else 55) else (if i.val < 23 then 81 else 86))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 81 else 85) else (if i.val < 27 then 55 else 55)) else (if i.val < 30 then (if i.val < 29 then 80 else 85) else (if i.val < 31 then 55 else 86))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 55 else 55) else (if i.val < 35 then 46 else 13)) else (if i.val < 38 then (if i.val < 37 then 55 else 81) else (if i.val < 39 then 45 else 56))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 25 else 11) else (if i.val < 43 then 84 else 11)) else (if i.val < 46 then (if i.val < 45 then 86 else 46) else (if i.val < 47 then 55 else 81)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 85 else 54) else (if i.val < 51 then 49 else 54)) else (if i.val < 54 then (if i.val < 53 then 86 else 54) else (if i.val < 55 then 86 else 86))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 86 else 45) else (if i.val < 59 then 11 else 86)) else (if i.val < 62 then (if i.val < 61 then 54 else 46) else (if i.val < 63 then 46 else 25)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 47 else 25) else (if i.val < 67 then 46 else 80)) else (if i.val < 70 then (if i.val < 69 then 55 else 49) else (if i.val < 71 then 49 else 86))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 46 else 11) else (if i.val < 75 then 80 else 84)) else (if i.val < 78 then (if i.val < 77 then 54 else 84) else (if i.val < 79 then 11 else 86)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 46 else 85) else (if i.val < 83 then 86 else 86)) else (if i.val < 86 then (if i.val < 85 then 45 else 86) else (if i.val < 87 then 26 else 80))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 53 else 86) else (if i.val < 91 then 86 else 47)) else (if i.val < 94 then (if i.val < 93 then 55 else 86) else (if i.val < 95 then 83 else 83))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 54 else 54) else (if i.val < 99 then 55 else 55)) else (if i.val < 102 then (if i.val < 101 then 81 else 47) else (if i.val < 103 then 26 else 11))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 81 else 13) else (if i.val < 107 then 25 else 86)) else (if i.val < 110 then (if i.val < 109 then 85 else 85) else (if i.val < 111 then 53 else 48)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 52 else 55) else (if i.val < 115 then 86 else 81)) else (if i.val < 118 then (if i.val < 117 then 13 else 47) else (if i.val < 119 then 86 else 83))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 86 else 53) else (if i.val < 123 then 26 else 86)) else (if i.val < 126 then (if i.val < 125 then 86 else 86) else (if i.val < 127 then 55 else 49))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 80 else 86) else (if i.val < 131 then 49 else 80)) else (if i.val < 134 then (if i.val < 133 then 11 else 80) else (if i.val < 135 then 80 else 86))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 54 else 86) else (if i.val < 139 then 86 else 45)) else (if i.val < 142 then (if i.val < 141 then 52 else 53) else (if i.val < 143 then 86 else 86)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 55 else 46) else (if i.val < 147 then 80 else 85)) else (if i.val < 150 then (if i.val < 149 then 86 else 55) else (if i.val < 151 then 52 else 46))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 46 else 98) else (if i.val < 155 then 55 else 52)) else (if i.val < 158 then (if i.val < 157 then 52 else 55) else (if i.val < 159 then 46 else 55))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 45 else 55) else (if i.val < 163 then 86 else 84)) else (if i.val < 166 then (if i.val < 165 then 11 else 86) else (if i.val < 167 then 26 else 86))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 55) else (if i.val < 171 then 13 else 49)) else (if i.val < 174 then (if i.val < 173 then 11 else 86) else (if i.val < 175 then 85 else 55)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 84 else 53) else (if i.val < 179 then 55 else 52)) else (if i.val < 182 then (if i.val < 181 then 81 else 80) else (if i.val < 183 then 55 else 85))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 56 else 86) else (if i.val < 187 then 52 else 54)) else (if i.val < 190 then (if i.val < 189 then 49 else 84) else (if i.val < 191 then 86 else 45)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 86 else 26) else (if i.val < 195 then 86 else 86)) else (if i.val < 198 then (if i.val < 197 then 86 else 55) else (if i.val < 199 then 11 else 86))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 45 else 86) else (if i.val < 203 then 54 else 50)) else (if i.val < 206 then (if i.val < 205 then 46 else 47) else (if i.val < 207 then 11 else 86)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 55 else 47) else (if i.val < 211 then 45 else 11)) else (if i.val < 214 then (if i.val < 213 then 86 else 84) else (if i.val < 215 then 86 else 26))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 85 else 86) else (if i.val < 219 then 26 else 55)) else (if i.val < 222 then (if i.val < 221 then 98 else 53) else (if i.val < 223 then 47 else 45))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 83 else 86) else (if i.val < 227 then 54 else 45)) else (if i.val < 230 then (if i.val < 229 then 45 else 86) else (if i.val < 231 then 86 else 85))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 86 else 86) else (if i.val < 235 then 86 else 86)) else (if i.val < 238 then (if i.val < 237 then 86 else 86) else (if i.val < 239 then 86 else 54)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 86 else 86) else (if i.val < 243 then 86 else 46)) else (if i.val < 246 then (if i.val < 245 then 86 else 53) else (if i.val < 247 then 26 else 86))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 80 else 26) else (if i.val < 251 then 86 else 26)) else (if i.val < 254 then (if i.val < 253 then 86 else 83) else (if i.val < 255 then 86 else 83))))))))

theorem g32p_supplierForest_actual_055 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_055 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_055 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_145178
  · exact g32p_supplierForest_actual_145179
  · exact g32p_supplierForest_actual_145203
  · exact g32p_supplierForest_actual_145210
  · exact g32p_supplierForest_actual_145226
  · exact g32p_supplierForest_actual_145261
  · exact g32p_supplierForest_actual_145287
  · exact g32p_supplierForest_actual_145311
  · exact g32p_supplierForest_actual_145345
  · exact g32p_supplierForest_actual_145406
  · exact g32p_supplierForest_actual_145411
  · exact g32p_supplierForest_actual_145443
  · exact g32p_supplierForest_actual_145451
  · exact g32p_supplierForest_actual_145460
  · exact g32p_supplierForest_actual_145484
  · exact g32p_supplierForest_actual_145575
  · exact g32p_supplierForest_actual_145589
  · exact g32p_supplierForest_actual_145617
  · exact g32p_supplierForest_actual_145621
  · exact g32p_supplierForest_actual_145642
  · exact g32p_supplierForest_actual_145681
  · exact g32p_supplierForest_actual_145705
  · exact g32p_supplierForest_actual_145721
  · exact g32p_supplierForest_actual_145736
  · exact g32p_supplierForest_actual_145770
  · exact g32p_supplierForest_actual_145778
  · exact g32p_supplierForest_actual_145786
  · exact g32p_supplierForest_actual_145820
  · exact g32p_supplierForest_actual_145832
  · exact g32p_supplierForest_actual_145859
  · exact g32p_supplierForest_actual_145912
  · exact g32p_supplierForest_actual_145934
  · exact g32p_supplierForest_actual_145967
  · exact g32p_supplierForest_actual_145986
  · exact g32p_supplierForest_actual_146002
  · exact g32p_supplierForest_actual_146018
  · exact g32p_supplierForest_actual_146023
  · exact g32p_supplierForest_actual_146066
  · exact g32p_supplierForest_actual_146099
  · exact g32p_supplierForest_actual_146109
  · exact g32p_supplierForest_actual_146151
  · exact g32p_supplierForest_actual_146154
  · exact g32p_supplierForest_actual_146181
  · exact g32p_supplierForest_actual_146198
  · exact g32p_supplierForest_actual_146202
  · exact g32p_supplierForest_actual_146218
  · exact g32p_supplierForest_actual_146238
  · exact g32p_supplierForest_actual_146264
  · exact g32p_supplierForest_actual_146315
  · exact g32p_supplierForest_actual_146328
  · exact g32p_supplierForest_actual_146359
  · exact g32p_supplierForest_actual_146361
  · exact g32p_supplierForest_actual_146403
  · exact g32p_supplierForest_actual_146418
  · exact g32p_supplierForest_actual_146431
  · exact g32p_supplierForest_actual_146499
  · exact g32p_supplierForest_actual_146505
  · exact g32p_supplierForest_actual_146519
  · exact g32p_supplierForest_actual_146526
  · exact g32p_supplierForest_actual_146527
  · exact g32p_supplierForest_actual_146576
  · exact g32p_supplierForest_actual_146620
  · exact g32p_supplierForest_actual_146639
  · exact g32p_supplierForest_actual_146650
  · exact g32p_supplierForest_actual_146744
  · exact g32p_supplierForest_actual_146750
  · exact g32p_supplierForest_actual_146788
  · exact g32p_supplierForest_actual_146794
  · exact g32p_supplierForest_actual_146811
  · exact g32p_supplierForest_actual_146820
  · exact g32p_supplierForest_actual_146827
  · exact g32p_supplierForest_actual_146829
  · exact g32p_supplierForest_actual_146836
  · exact g32p_supplierForest_actual_146853
  · exact g32p_supplierForest_actual_146857
  · exact g32p_supplierForest_actual_146869
  · exact g32p_supplierForest_actual_146881
  · exact g32p_supplierForest_actual_146896
  · exact g32p_supplierForest_actual_146957
  · exact g32p_supplierForest_actual_146963
  · exact g32p_supplierForest_actual_146978
  · exact g32p_supplierForest_actual_146994
  · exact g32p_supplierForest_actual_147010
  · exact g32p_supplierForest_actual_147016
  · exact g32p_supplierForest_actual_147052
  · exact g32p_supplierForest_actual_147055
  · exact g32p_supplierForest_actual_147056
  · exact g32p_supplierForest_actual_147062
  · exact g32p_supplierForest_actual_147105
  · exact g32p_supplierForest_actual_147191
  · exact g32p_supplierForest_actual_147248
  · exact g32p_supplierForest_actual_147289
  · exact g32p_supplierForest_actual_147300
  · exact g32p_supplierForest_actual_147301
  · exact g32p_supplierForest_actual_147336
  · exact g32p_supplierForest_actual_147342
  · exact g32p_supplierForest_actual_147370
  · exact g32p_supplierForest_actual_147430
  · exact g32p_supplierForest_actual_147441
  · exact g32p_supplierForest_actual_147459
  · exact g32p_supplierForest_actual_147464
  · exact g32p_supplierForest_actual_147475
  · exact g32p_supplierForest_actual_147508
  · exact g32p_supplierForest_actual_147527
  · exact g32p_supplierForest_actual_147583
  · exact g32p_supplierForest_actual_147632
  · exact g32p_supplierForest_actual_147749
  · exact g32p_supplierForest_actual_147780
  · exact g32p_supplierForest_actual_147786
  · exact g32p_supplierForest_actual_147790
  · exact g32p_supplierForest_actual_147792
  · exact g32p_supplierForest_actual_147873
  · exact g32p_supplierForest_actual_147878
  · exact g32p_supplierForest_actual_147907
  · exact g32p_supplierForest_actual_147954
  · exact g32p_supplierForest_actual_147973
  · exact g32p_supplierForest_actual_147984
  · exact g32p_supplierForest_actual_148006
  · exact g32p_supplierForest_actual_148008
  · exact g32p_supplierForest_actual_148044
  · exact g32p_supplierForest_actual_148113
  · exact g32p_supplierForest_actual_148115
  · exact g32p_supplierForest_actual_148129
  · exact g32p_supplierForest_actual_148183
  · exact g32p_supplierForest_actual_148191
  · exact g32p_supplierForest_actual_148195
  · exact g32p_supplierForest_actual_148264
  · exact g32p_supplierForest_actual_148273
  · exact g32p_supplierForest_actual_148299
  · exact g32p_supplierForest_actual_148340
  · exact g32p_supplierForest_actual_148404
  · exact g32p_supplierForest_actual_148429
  · exact g32p_supplierForest_actual_148451
  · exact g32p_supplierForest_actual_148453
  · exact g32p_supplierForest_actual_148461
  · exact g32p_supplierForest_actual_148467
  · exact g32p_supplierForest_actual_148487
  · exact g32p_supplierForest_actual_148567
  · exact g32p_supplierForest_actual_148618
  · exact g32p_supplierForest_actual_148690
  · exact g32p_supplierForest_actual_148691
  · exact g32p_supplierForest_actual_148701
  · exact g32p_supplierForest_actual_148754
  · exact g32p_supplierForest_actual_148770
  · exact g32p_supplierForest_actual_148786
  · exact g32p_supplierForest_actual_148823
  · exact g32p_supplierForest_actual_148839
  · exact g32p_supplierForest_actual_148845
  · exact g32p_supplierForest_actual_148865
  · exact g32p_supplierForest_actual_148903
  · exact g32p_supplierForest_actual_148909
  · exact g32p_supplierForest_actual_148912
  · exact g32p_supplierForest_actual_148913
  · exact g32p_supplierForest_actual_148994
  · exact g32p_supplierForest_actual_149029
  · exact g32p_supplierForest_actual_149045
  · exact g32p_supplierForest_actual_149077
  · exact g32p_supplierForest_actual_149131
  · exact g32p_supplierForest_actual_149138
  · exact g32p_supplierForest_actual_149175
  · exact g32p_supplierForest_actual_149178
  · exact g32p_supplierForest_actual_149188
  · exact g32p_supplierForest_actual_149224
  · exact g32p_supplierForest_actual_149255
  · exact g32p_supplierForest_actual_149307
  · exact g32p_supplierForest_actual_149328
  · exact g32p_supplierForest_actual_149333
  · exact g32p_supplierForest_actual_149355
  · exact g32p_supplierForest_actual_149357
  · exact g32p_supplierForest_actual_149367
  · exact g32p_supplierForest_actual_149381
  · exact g32p_supplierForest_actual_149416
  · exact g32p_supplierForest_actual_149434
  · exact g32p_supplierForest_actual_149465
  · exact g32p_supplierForest_actual_149473
  · exact g32p_supplierForest_actual_149490
  · exact g32p_supplierForest_actual_149555
  · exact g32p_supplierForest_actual_149632
  · exact g32p_supplierForest_actual_149633
  · exact g32p_supplierForest_actual_149766
  · exact g32p_supplierForest_actual_149803
  · exact g32p_supplierForest_actual_149829
  · exact g32p_supplierForest_actual_149830
  · exact g32p_supplierForest_actual_149845
  · exact g32p_supplierForest_actual_149885
  · exact g32p_supplierForest_actual_149892
  · exact g32p_supplierForest_actual_149902
  · exact g32p_supplierForest_actual_149909
  · exact g32p_supplierForest_actual_149985
  · exact g32p_supplierForest_actual_149992
  · exact g32p_supplierForest_actual_150117
  · exact g32p_supplierForest_actual_150162
  · exact g32p_supplierForest_actual_150177
  · exact g32p_supplierForest_actual_150187
  · exact g32p_supplierForest_actual_150196
  · exact g32p_supplierForest_actual_150198
  · exact g32p_supplierForest_actual_150265
  · exact g32p_supplierForest_actual_150282
  · exact g32p_supplierForest_actual_150313
  · exact g32p_supplierForest_actual_150329
  · exact g32p_supplierForest_actual_150366
  · exact g32p_supplierForest_actual_150386
  · exact g32p_supplierForest_actual_150464
  · exact g32p_supplierForest_actual_150493
  · exact g32p_supplierForest_actual_150502
  · exact g32p_supplierForest_actual_150537
  · exact g32p_supplierForest_actual_150552
  · exact g32p_supplierForest_actual_150676
  · exact g32p_supplierForest_actual_150689
  · exact g32p_supplierForest_actual_150700
  · exact g32p_supplierForest_actual_150724
  · exact g32p_supplierForest_actual_150761
  · exact g32p_supplierForest_actual_150787
  · exact g32p_supplierForest_actual_150834
  · exact g32p_supplierForest_actual_150902
  · exact g32p_supplierForest_actual_151034
  · exact g32p_supplierForest_actual_151055
  · exact g32p_supplierForest_actual_151097
  · exact g32p_supplierForest_actual_151204
  · exact g32p_supplierForest_actual_151209
  · exact g32p_supplierForest_actual_151246
  · exact g32p_supplierForest_actual_151253
  · exact g32p_supplierForest_actual_151286
  · exact g32p_supplierForest_actual_151333
  · exact g32p_supplierForest_actual_151386
  · exact g32p_supplierForest_actual_151403
  · exact g32p_supplierForest_actual_151431
  · exact g32p_supplierForest_actual_151441
  · exact g32p_supplierForest_actual_151574
  · exact g32p_supplierForest_actual_151588
  · exact g32p_supplierForest_actual_151608
  · exact g32p_supplierForest_actual_151651
  · exact g32p_supplierForest_actual_151670
  · exact g32p_supplierForest_actual_151680
  · exact g32p_supplierForest_actual_151682
  · exact g32p_supplierForest_actual_151686
  · exact g32p_supplierForest_actual_151701
  · exact g32p_supplierForest_actual_151724
  · exact g32p_supplierForest_actual_151751
  · exact g32p_supplierForest_actual_151754
  · exact g32p_supplierForest_actual_151785
  · exact g32p_supplierForest_actual_151803
  · exact g32p_supplierForest_actual_151815
  · exact g32p_supplierForest_actual_151823
  · exact g32p_supplierForest_actual_151840
  · exact g32p_supplierForest_actual_151862
  · exact g32p_supplierForest_actual_151901
  · exact g32p_supplierForest_actual_151978
  · exact g32p_supplierForest_actual_152007
  · exact g32p_supplierForest_actual_152015
  · exact g32p_supplierForest_actual_152019
  · exact g32p_supplierForest_actual_152208
  · exact g32p_supplierForest_actual_152211
  · exact g32p_supplierForest_actual_152218
  · exact g32p_supplierForest_actual_152257
  · exact g32p_supplierForest_actual_152298

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_152303 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152303 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152303 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_148509 := by
  decide +kernel

theorem g32p_supplierForest_actual_152303 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152303) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 1 g32p_supplierForest_edge_152303
    g32p_supplierForest_actual_148509

def g32p_supplierForest_node_152316 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152316 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152316 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099608 := by
  decide +kernel

theorem g32p_supplierForest_actual_152316 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152316) ∧
        IsConj g (g32p_literalRepresentative 11) := by
  exact g32p_archive_step_lift _ _ 11 1 g32p_supplierForest_edge_152316
    g32p_supplierForest_actual_099608

def g32p_supplierForest_node_152317 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152317 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152317 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_100183 := by
  decide +kernel

theorem g32p_supplierForest_actual_152317 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152317) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 3 g32p_supplierForest_edge_152317
    g32p_supplierForest_actual_100183

def g32p_supplierForest_node_152332 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152332 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152332 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146409 := by
  decide +kernel

theorem g32p_supplierForest_actual_152332 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152332) ∧
        IsConj g (g32p_literalRepresentative 83) := by
  exact g32p_archive_step_lift _ _ 83 2 g32p_supplierForest_edge_152332
    g32p_supplierForest_actual_146409

def g32p_supplierForest_node_152352 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_152352 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152352 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_146950 := by
  decide +kernel

theorem g32p_supplierForest_actual_152352 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152352) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_152352
    g32p_supplierForest_actual_146950

def g32p_supplierForest_node_152369 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152369 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152369 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095023 := by
  decide +kernel

theorem g32p_supplierForest_actual_152369 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152369) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_152369
    g32p_supplierForest_actual_095023

def g32p_supplierForest_node_152398 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152398 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152398 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_147406 := by
  decide +kernel

theorem g32p_supplierForest_actual_152398 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152398) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 1 g32p_supplierForest_edge_152398
    g32p_supplierForest_actual_147406

def g32p_supplierForest_node_152419 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152419 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152419 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152394 := by
  decide +kernel

theorem g32p_supplierForest_actual_152419 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152419) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_152419
    g32p_supplierForest_actual_152394

def g32p_supplierForest_node_152432 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_152432 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152432 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151379 := by
  decide +kernel

theorem g32p_supplierForest_actual_152432 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152432) ∧
        IsConj g (g32p_literalRepresentative 98) := by
  exact g32p_archive_step_lift _ _ 98 0 g32p_supplierForest_edge_152432
    g32p_supplierForest_actual_151379

def g32p_supplierForest_node_152460 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152460 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152460 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_148703 := by
  decide +kernel

theorem g32p_supplierForest_actual_152460 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152460) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 2 g32p_supplierForest_edge_152460
    g32p_supplierForest_actual_148703

def g32p_supplierForest_node_152490 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_152490 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152490 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_151452 := by
  decide +kernel

theorem g32p_supplierForest_actual_152490 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152490) ∧
        IsConj g (g32p_literalRepresentative 86) := by
  exact g32p_archive_step_lift _ _ 86 0 g32p_supplierForest_edge_152490
    g32p_supplierForest_actual_151452

def g32p_supplierForest_node_152493 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_152493 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152493 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_101404 := by
  decide +kernel

theorem g32p_supplierForest_actual_152493 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152493) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 3 g32p_supplierForest_edge_152493
    g32p_supplierForest_actual_101404

def g32p_supplierForest_node_152501 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152501 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152501 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099609 := by
  decide +kernel

theorem g32p_supplierForest_actual_152501 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152501) ∧
        IsConj g (g32p_literalRepresentative 85) := by
  exact g32p_archive_step_lift _ _ 85 3 g32p_supplierForest_edge_152501
    g32p_supplierForest_actual_099609

def g32p_supplierForest_node_152512 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152512 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152512 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109920 := by
  decide +kernel

theorem g32p_supplierForest_actual_152512 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152512) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_152512
    g32p_supplierForest_actual_109920

def g32p_supplierForest_node_152559 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152559 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152559 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112619 := by
  decide +kernel

theorem g32p_supplierForest_actual_152559 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152559) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_152559
    g32p_supplierForest_actual_112619

def g32p_supplierForest_node_152567 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152567 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152567 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152656 := by
  decide +kernel

theorem g32p_supplierForest_actual_152567 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152567) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_152567
    g32p_supplierForest_actual_152656

def g32p_supplierForest_node_152571 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152571 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152571 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154706 := by
  decide +kernel

theorem g32p_supplierForest_actual_152571 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152571) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_152571
    g32p_supplierForest_actual_154706

def g32p_supplierForest_node_152572 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152572 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152572 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_152533 := by
  decide +kernel

theorem g32p_supplierForest_actual_152572 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152572) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_152572
    g32p_supplierForest_actual_152533

def g32p_supplierForest_node_152605 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152605 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152605 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121506 := by
  decide +kernel

theorem g32p_supplierForest_actual_152605 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152605) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_152605
    g32p_supplierForest_actual_121506

def g32p_supplierForest_node_152608 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152608 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152608 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_120378 := by
  decide +kernel

theorem g32p_supplierForest_actual_152608 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152608) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_152608
    g32p_supplierForest_actual_120378

def g32p_supplierForest_node_152616 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152616 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152616 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122623 := by
  decide +kernel

theorem g32p_supplierForest_actual_152616 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152616) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_152616
    g32p_supplierForest_actual_122623

def g32p_supplierForest_node_152713 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152713 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152713 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154513 := by
  decide +kernel

theorem g32p_supplierForest_actual_152713 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152713) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_152713
    g32p_supplierForest_actual_154513

def g32p_supplierForest_node_152758 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152758 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152758 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126916 := by
  decide +kernel

theorem g32p_supplierForest_actual_152758 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152758) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_152758
    g32p_supplierForest_actual_126916

def g32p_supplierForest_node_152780 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152780 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152780 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153238 := by
  decide +kernel

theorem g32p_supplierForest_actual_152780 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152780) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_152780
    g32p_supplierForest_actual_153238

def g32p_supplierForest_node_152792 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152792 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152792 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127502 := by
  decide +kernel

theorem g32p_supplierForest_actual_152792 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152792) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_152792
    g32p_supplierForest_actual_127502

def g32p_supplierForest_node_152801 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152801 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154643 := by
  decide +kernel

theorem g32p_supplierForest_actual_152801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152801) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_152801
    g32p_supplierForest_actual_154643

def g32p_supplierForest_node_152802 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_152802 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152802 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154643 := by
  decide +kernel

theorem g32p_supplierForest_actual_152802 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152802) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_152802
    g32p_supplierForest_actual_154643

def g32p_supplierForest_node_152846 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_152846 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152846 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118033 := by
  decide +kernel

theorem g32p_supplierForest_actual_152846 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152846) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 3 g32p_supplierForest_edge_152846
    g32p_supplierForest_actual_118033

def g32p_supplierForest_node_152891 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_152891 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152891 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102052 := by
  decide +kernel

theorem g32p_supplierForest_actual_152891 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152891) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_152891
    g32p_supplierForest_actual_102052

def g32p_supplierForest_node_152942 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152942 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152942 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_116237 := by
  decide +kernel

theorem g32p_supplierForest_actual_152942 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152942) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_152942
    g32p_supplierForest_actual_116237

def g32p_supplierForest_node_152952 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_152952 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_152952 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122940 := by
  decide +kernel

theorem g32p_supplierForest_actual_152952 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_152952) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_152952
    g32p_supplierForest_actual_122940

def g32p_supplierForest_node_153008 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153008 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153008 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126981 := by
  decide +kernel

theorem g32p_supplierForest_actual_153008 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153008) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_153008
    g32p_supplierForest_actual_126981

def g32p_supplierForest_node_153012 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153012 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153012 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153901 := by
  decide +kernel

theorem g32p_supplierForest_actual_153012 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153012) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_153012
    g32p_supplierForest_actual_153901

def g32p_supplierForest_node_153035 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153035 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153035 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_107933 := by
  decide +kernel

theorem g32p_supplierForest_actual_153035 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153035) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_153035
    g32p_supplierForest_actual_107933

def g32p_supplierForest_node_153047 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153047 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153047 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_123365 := by
  decide +kernel

theorem g32p_supplierForest_actual_153047 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153047) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_153047
    g32p_supplierForest_actual_123365

def g32p_supplierForest_node_153065 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153065 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153065 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122198 := by
  decide +kernel

theorem g32p_supplierForest_actual_153065 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153065) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_153065
    g32p_supplierForest_actual_122198

def g32p_supplierForest_node_153096 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153096 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153096 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_116158 := by
  decide +kernel

theorem g32p_supplierForest_actual_153096 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153096) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_153096
    g32p_supplierForest_actual_116158

def g32p_supplierForest_node_153099 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153099 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153099 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154803 := by
  decide +kernel

theorem g32p_supplierForest_actual_153099 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153099) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_153099
    g32p_supplierForest_actual_154803

def g32p_supplierForest_node_153107 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_153107 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153107 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_105541 := by
  decide +kernel

theorem g32p_supplierForest_actual_153107 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153107) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_153107
    g32p_supplierForest_actual_105541

def g32p_supplierForest_node_153128 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153128 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153128 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154108 := by
  decide +kernel

theorem g32p_supplierForest_actual_153128 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153128) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 0 g32p_supplierForest_edge_153128
    g32p_supplierForest_actual_154108

def g32p_supplierForest_node_153160 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153160 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153160 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154461 := by
  decide +kernel

theorem g32p_supplierForest_actual_153160 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153160) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_153160
    g32p_supplierForest_actual_154461

def g32p_supplierForest_node_153199 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153199 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153199 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154115 := by
  decide +kernel

theorem g32p_supplierForest_actual_153199 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153199) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_153199
    g32p_supplierForest_actual_154115

def g32p_supplierForest_node_153209 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153209 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153209 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124078 := by
  decide +kernel

theorem g32p_supplierForest_actual_153209 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153209) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 0 g32p_supplierForest_edge_153209
    g32p_supplierForest_actual_124078

def g32p_supplierForest_node_153211 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153211 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153211 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154218 := by
  decide +kernel

theorem g32p_supplierForest_actual_153211 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153211) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_153211
    g32p_supplierForest_actual_154218

def g32p_supplierForest_node_153218 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_153218 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153218 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121215 := by
  decide +kernel

theorem g32p_supplierForest_actual_153218 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153218) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 1 g32p_supplierForest_edge_153218
    g32p_supplierForest_actual_121215

def g32p_supplierForest_node_153227 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153227 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153227 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_107894 := by
  decide +kernel

theorem g32p_supplierForest_actual_153227 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153227) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_153227
    g32p_supplierForest_actual_107894

def g32p_supplierForest_node_153236 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_153236 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153236 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114280 := by
  decide +kernel

theorem g32p_supplierForest_actual_153236 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153236) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_153236
    g32p_supplierForest_actual_114280

def g32p_supplierForest_node_153239 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153239 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153239 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126703 := by
  decide +kernel

theorem g32p_supplierForest_actual_153239 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153239) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_153239
    g32p_supplierForest_actual_126703

def g32p_supplierForest_node_153244 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_153244 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153244 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153964 := by
  decide +kernel

theorem g32p_supplierForest_actual_153244 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153244) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_153244
    g32p_supplierForest_actual_153964

def g32p_supplierForest_node_153248 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153248 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153248 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_125341 := by
  decide +kernel

theorem g32p_supplierForest_actual_153248 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153248) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_153248
    g32p_supplierForest_actual_125341

def g32p_supplierForest_node_153255 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_153255 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153255 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113426 := by
  decide +kernel

theorem g32p_supplierForest_actual_153255 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153255) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_153255
    g32p_supplierForest_actual_113426

def g32p_supplierForest_node_153262 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_153262 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153262 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117188 := by
  decide +kernel

theorem g32p_supplierForest_actual_153262 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153262) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_153262
    g32p_supplierForest_actual_117188

def g32p_supplierForest_node_153331 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_153331 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153331 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122957 := by
  decide +kernel

theorem g32p_supplierForest_actual_153331 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153331) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_153331
    g32p_supplierForest_actual_122957

def g32p_supplierForest_node_153334 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153334 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153487 := by
  decide +kernel

theorem g32p_supplierForest_actual_153334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153334) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_153334
    g32p_supplierForest_actual_153487

def g32p_supplierForest_node_153355 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153355 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153355 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109622 := by
  decide +kernel

theorem g32p_supplierForest_actual_153355 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153355) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 1 g32p_supplierForest_edge_153355
    g32p_supplierForest_actual_109622

def g32p_supplierForest_node_153361 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_153361 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153361 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127158 := by
  decide +kernel

theorem g32p_supplierForest_actual_153361 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153361) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_153361
    g32p_supplierForest_actual_127158

def g32p_supplierForest_node_153365 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153365 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153365 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153542 := by
  decide +kernel

theorem g32p_supplierForest_actual_153365 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153365) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 1 g32p_supplierForest_edge_153365
    g32p_supplierForest_actual_153542

def g32p_supplierForest_node_153377 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153377 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153377 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127700 := by
  decide +kernel

theorem g32p_supplierForest_actual_153377 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153377) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_153377
    g32p_supplierForest_actual_127700

def g32p_supplierForest_node_153383 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153383 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153383 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_119726 := by
  decide +kernel

theorem g32p_supplierForest_actual_153383 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153383) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_153383
    g32p_supplierForest_actual_119726

def g32p_supplierForest_node_153420 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153420 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153420 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124078 := by
  decide +kernel

theorem g32p_supplierForest_actual_153420 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153420) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_153420
    g32p_supplierForest_actual_124078

def g32p_supplierForest_node_153445 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153445 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126615 := by
  decide +kernel

theorem g32p_supplierForest_actual_153445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153445) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_153445
    g32p_supplierForest_actual_126615

def g32p_supplierForest_node_153449 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153449 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153449 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121064 := by
  decide +kernel

theorem g32p_supplierForest_actual_153449 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153449) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 0 g32p_supplierForest_edge_153449
    g32p_supplierForest_actual_121064

def g32p_supplierForest_node_153482 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153482 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153482 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117662 := by
  decide +kernel

theorem g32p_supplierForest_actual_153482 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153482) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_153482
    g32p_supplierForest_actual_117662

def g32p_supplierForest_node_153500 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153500 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153500 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_107828 := by
  decide +kernel

theorem g32p_supplierForest_actual_153500 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153500) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_153500
    g32p_supplierForest_actual_107828

def g32p_supplierForest_node_153503 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153503 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153503 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126415 := by
  decide +kernel

theorem g32p_supplierForest_actual_153503 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153503) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_153503
    g32p_supplierForest_actual_126415

def g32p_supplierForest_node_153518 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_153518 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153518 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_124850 := by
  decide +kernel

theorem g32p_supplierForest_actual_153518 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153518) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_153518
    g32p_supplierForest_actual_124850

def g32p_supplierForest_node_153523 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_153523 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153523 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152842 := by
  decide +kernel

theorem g32p_supplierForest_actual_153523 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153523) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_153523
    g32p_supplierForest_actual_152842

def g32p_supplierForest_node_153529 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153529 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_105573 := by
  decide +kernel

theorem g32p_supplierForest_actual_153529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153529) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_153529
    g32p_supplierForest_actual_105573

def g32p_supplierForest_node_153536 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153536 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153536 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124569 := by
  decide +kernel

theorem g32p_supplierForest_actual_153536 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153536) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_153536
    g32p_supplierForest_actual_124569

def g32p_supplierForest_node_153559 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153559 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153559 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122959 := by
  decide +kernel

theorem g32p_supplierForest_actual_153559 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153559) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_153559
    g32p_supplierForest_actual_122959

def g32p_supplierForest_node_153594 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_153594 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153594 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153994 := by
  decide +kernel

theorem g32p_supplierForest_actual_153594 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153594) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 2 g32p_supplierForest_edge_153594
    g32p_supplierForest_actual_153994

def g32p_supplierForest_node_153597 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153597 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153597 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_125189 := by
  decide +kernel

theorem g32p_supplierForest_actual_153597 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153597) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_153597
    g32p_supplierForest_actual_125189

def g32p_supplierForest_node_153615 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153615 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153615 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_125539 := by
  decide +kernel

theorem g32p_supplierForest_actual_153615 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153615) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_153615
    g32p_supplierForest_actual_125539

def g32p_supplierForest_node_153645 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153645 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153645 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_125542 := by
  decide +kernel

theorem g32p_supplierForest_actual_153645 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153645) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_153645
    g32p_supplierForest_actual_125542

def g32p_supplierForest_node_153670 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153670 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153670 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153606 := by
  decide +kernel

theorem g32p_supplierForest_actual_153670 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153670) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_153670
    g32p_supplierForest_actual_153606

def g32p_supplierForest_node_153708 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153708 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153708 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153578 := by
  decide +kernel

theorem g32p_supplierForest_actual_153708 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153708) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_153708
    g32p_supplierForest_actual_153578

def g32p_supplierForest_node_153711 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_153711 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153711 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_120355 := by
  decide +kernel

theorem g32p_supplierForest_actual_153711 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153711) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 3 g32p_supplierForest_edge_153711
    g32p_supplierForest_actual_120355

def g32p_supplierForest_node_153712 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153712 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153712 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110376 := by
  decide +kernel

theorem g32p_supplierForest_actual_153712 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153712) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_153712
    g32p_supplierForest_actual_110376

def g32p_supplierForest_node_153732 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153732 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116581 := by
  decide +kernel

theorem g32p_supplierForest_actual_153732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153732) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_153732
    g32p_supplierForest_actual_116581

def g32p_supplierForest_node_153783 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153783 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153877 := by
  decide +kernel

theorem g32p_supplierForest_actual_153783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153783) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_153783
    g32p_supplierForest_actual_153877

def g32p_supplierForest_node_153793 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_153793 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153793 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153885 := by
  decide +kernel

theorem g32p_supplierForest_actual_153793 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153793) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_153793
    g32p_supplierForest_actual_153885

def g32p_supplierForest_node_153798 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153798 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153798 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122684 := by
  decide +kernel

theorem g32p_supplierForest_actual_153798 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153798) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_153798
    g32p_supplierForest_actual_122684

def g32p_supplierForest_node_153835 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153835 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153835 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126378 := by
  decide +kernel

theorem g32p_supplierForest_actual_153835 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153835) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_153835
    g32p_supplierForest_actual_126378

def g32p_supplierForest_node_153837 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153837 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153837 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116737 := by
  decide +kernel

theorem g32p_supplierForest_actual_153837 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153837) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_153837
    g32p_supplierForest_actual_116737

def g32p_supplierForest_node_153861 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_153861 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153861 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153784 := by
  decide +kernel

theorem g32p_supplierForest_actual_153861 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153861) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_153861
    g32p_supplierForest_actual_153784

def g32p_supplierForest_node_153909 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_153909 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153909 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126832 := by
  decide +kernel

theorem g32p_supplierForest_actual_153909 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153909) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_153909
    g32p_supplierForest_actual_126832

def g32p_supplierForest_node_153963 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_153963 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153963 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153326 := by
  decide +kernel

theorem g32p_supplierForest_actual_153963 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153963) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_153963
    g32p_supplierForest_actual_153326

def g32p_supplierForest_node_153969 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_153969 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153969 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154798 := by
  decide +kernel

theorem g32p_supplierForest_actual_153969 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153969) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_153969
    g32p_supplierForest_actual_154798

def g32p_supplierForest_node_153980 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_153980 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_153980 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153487 := by
  decide +kernel

theorem g32p_supplierForest_actual_153980 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_153980) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 3 g32p_supplierForest_edge_153980
    g32p_supplierForest_actual_153487

def g32p_supplierForest_node_154009 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_154009 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154009 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123633 := by
  decide +kernel

theorem g32p_supplierForest_actual_154009 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154009) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_154009
    g32p_supplierForest_actual_123633

def g32p_supplierForest_node_154040 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154040 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_124561 := by
  decide +kernel

theorem g32p_supplierForest_actual_154040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154040) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_154040
    g32p_supplierForest_actual_124561

def g32p_supplierForest_node_154063 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154063 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154063 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_126160 := by
  decide +kernel

theorem g32p_supplierForest_actual_154063 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154063) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_154063
    g32p_supplierForest_actual_126160

def g32p_supplierForest_node_154130 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154130 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154130 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_126375 := by
  decide +kernel

theorem g32p_supplierForest_actual_154130 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154130) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_154130
    g32p_supplierForest_actual_126375

def g32p_supplierForest_node_154154 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154154 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154154 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118432 := by
  decide +kernel

theorem g32p_supplierForest_actual_154154 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154154) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_154154
    g32p_supplierForest_actual_118432

def g32p_supplierForest_node_154171 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154171 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153201 := by
  decide +kernel

theorem g32p_supplierForest_actual_154171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154171) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_154171
    g32p_supplierForest_actual_153201

def g32p_supplierForest_node_154246 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154246 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117551 := by
  decide +kernel

theorem g32p_supplierForest_actual_154246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154246) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_154246
    g32p_supplierForest_actual_117551

def g32p_supplierForest_node_154278 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154278 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154278 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154874 := by
  decide +kernel

theorem g32p_supplierForest_actual_154278 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154278) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 1 g32p_supplierForest_edge_154278
    g32p_supplierForest_actual_154874

def g32p_supplierForest_node_154322 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154322 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154322 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153784 := by
  decide +kernel

theorem g32p_supplierForest_actual_154322 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154322) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 0 g32p_supplierForest_edge_154322
    g32p_supplierForest_actual_153784

def g32p_supplierForest_node_154353 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154353 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154353 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115782 := by
  decide +kernel

theorem g32p_supplierForest_actual_154353 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154353) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_154353
    g32p_supplierForest_actual_115782

def g32p_supplierForest_node_154439 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154439 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123796 := by
  decide +kernel

theorem g32p_supplierForest_actual_154439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154439) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_154439
    g32p_supplierForest_actual_123796

def g32p_supplierForest_node_154456 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_154456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154456 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127791 := by
  decide +kernel

theorem g32p_supplierForest_actual_154456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154456) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 0 g32p_supplierForest_edge_154456
    g32p_supplierForest_actual_127791

def g32p_supplierForest_node_154466 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154466 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154466 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_153998 := by
  decide +kernel

theorem g32p_supplierForest_actual_154466 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154466) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_154466
    g32p_supplierForest_actual_153998

def g32p_supplierForest_node_154479 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154479 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154479 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_122513 := by
  decide +kernel

theorem g32p_supplierForest_actual_154479 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154479) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 2 g32p_supplierForest_edge_154479
    g32p_supplierForest_actual_122513

def g32p_supplierForest_node_154517 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154517 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154517 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117357 := by
  decide +kernel

theorem g32p_supplierForest_actual_154517 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154517) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 3 g32p_supplierForest_edge_154517
    g32p_supplierForest_actual_117357

def g32p_supplierForest_node_154522 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154522 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126958 := by
  decide +kernel

theorem g32p_supplierForest_actual_154522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154522) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_154522
    g32p_supplierForest_actual_126958

def g32p_supplierForest_node_154526 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154526 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154526 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122510 := by
  decide +kernel

theorem g32p_supplierForest_actual_154526 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154526) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_154526
    g32p_supplierForest_actual_122510

def g32p_supplierForest_node_154539 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154539 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153011 := by
  decide +kernel

theorem g32p_supplierForest_actual_154539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154539) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 1 g32p_supplierForest_edge_154539
    g32p_supplierForest_actual_153011

def g32p_supplierForest_node_154545 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_154545 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154545 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_126793 := by
  decide +kernel

theorem g32p_supplierForest_actual_154545 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154545) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 2 g32p_supplierForest_edge_154545
    g32p_supplierForest_actual_126793

def g32p_supplierForest_node_154702 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154702 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154702 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154046 := by
  decide +kernel

theorem g32p_supplierForest_actual_154702 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154702) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_154702
    g32p_supplierForest_actual_154046

def g32p_supplierForest_node_154749 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154749 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154749 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_153297 := by
  decide +kernel

theorem g32p_supplierForest_actual_154749 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154749) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 0 g32p_supplierForest_edge_154749
    g32p_supplierForest_actual_153297

def g32p_supplierForest_node_154773 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154773 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_154954 := by
  decide +kernel

theorem g32p_supplierForest_actual_154773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154773) ∧
        IsConj g (g32p_literalRepresentative 92) := by
  exact g32p_archive_step_lift _ _ 92 0 g32p_supplierForest_edge_154773
    g32p_supplierForest_actual_154954

def g32p_supplierForest_node_154806 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154806 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154806 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116631 := by
  decide +kernel

theorem g32p_supplierForest_actual_154806 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154806) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_154806
    g32p_supplierForest_actual_116631

def g32p_supplierForest_node_154867 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_154867 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154867 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_125928 := by
  decide +kernel

theorem g32p_supplierForest_actual_154867 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154867) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_154867
    g32p_supplierForest_actual_125928

def g32p_supplierForest_node_154881 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_154881 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154881 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154626 := by
  decide +kernel

theorem g32p_supplierForest_actual_154881 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154881) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_154881
    g32p_supplierForest_actual_154626

def g32p_supplierForest_node_154893 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154893 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154893 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_154567 := by
  decide +kernel

theorem g32p_supplierForest_actual_154893 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154893) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 2 g32p_supplierForest_edge_154893
    g32p_supplierForest_actual_154567

def g32p_supplierForest_node_154899 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154899 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154899 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_125539 := by
  decide +kernel

theorem g32p_supplierForest_actual_154899 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154899) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_154899
    g32p_supplierForest_actual_125539

def g32p_supplierForest_node_154931 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_154931 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154931 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_154245 := by
  decide +kernel

theorem g32p_supplierForest_actual_154931 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154931) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_154931
    g32p_supplierForest_actual_154245

def g32p_supplierForest_node_154938 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_154938 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154938 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152595 := by
  decide +kernel

theorem g32p_supplierForest_actual_154938 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154938) ∧
        IsConj g (g32p_literalRepresentative 89) := by
  exact g32p_archive_step_lift _ _ 89 3 g32p_supplierForest_edge_154938
    g32p_supplierForest_actual_152595

def g32p_supplierForest_node_154973 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154973 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154973 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152582 := by
  decide +kernel

theorem g32p_supplierForest_actual_154973 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154973) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_154973
    g32p_supplierForest_actual_152582

def g32p_supplierForest_node_154996 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_154996 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_154996 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_152796 := by
  decide +kernel

theorem g32p_supplierForest_actual_154996 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_154996) ∧
        IsConj g (g32p_literalRepresentative 90) := by
  exact g32p_archive_step_lift _ _ 90 3 g32p_supplierForest_edge_154996
    g32p_supplierForest_actual_152796

def g32p_supplierForest_node_155035 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155035 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155035 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155254 := by
  decide +kernel

theorem g32p_supplierForest_actual_155035 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155035) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 2 g32p_supplierForest_edge_155035
    g32p_supplierForest_actual_155254

def g32p_supplierForest_node_155036 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155036 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155036 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_134020 := by
  decide +kernel

theorem g32p_supplierForest_actual_155036 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155036) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 3 g32p_supplierForest_edge_155036
    g32p_supplierForest_actual_134020

def g32p_supplierForest_node_155083 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155083 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155083 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_134824 := by
  decide +kernel

theorem g32p_supplierForest_actual_155083 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155083) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 2 g32p_supplierForest_edge_155083
    g32p_supplierForest_actual_134824

def g32p_supplierForest_node_155102 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155102 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155102 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155315 := by
  decide +kernel

theorem g32p_supplierForest_actual_155102 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155102) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 1 g32p_supplierForest_edge_155102
    g32p_supplierForest_actual_155315

def g32p_supplierForest_node_155113 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155113 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_144144 := by
  decide +kernel

theorem g32p_supplierForest_actual_155113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155113) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 3 g32p_supplierForest_edge_155113
    g32p_supplierForest_actual_144144

def g32p_supplierForest_node_155119 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_155119 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155119 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_140977 := by
  decide +kernel

theorem g32p_supplierForest_actual_155119 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155119) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_155119
    g32p_supplierForest_actual_140977

def g32p_supplierForest_node_155135 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155135 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155135 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_155407 := by
  decide +kernel

theorem g32p_supplierForest_actual_155135 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155135) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 3 g32p_supplierForest_edge_155135
    g32p_supplierForest_actual_155407

def g32p_supplierForest_node_155141 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_155141 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155141 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155311 := by
  decide +kernel

theorem g32p_supplierForest_actual_155141 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155141) ∧
        IsConj g (g32p_literalRepresentative 94) := by
  exact g32p_archive_step_lift _ _ 94 1 g32p_supplierForest_edge_155141
    g32p_supplierForest_actual_155311

def g32p_supplierForest_node_155144 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155144 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155144 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_144594 := by
  decide +kernel

theorem g32p_supplierForest_actual_155144 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155144) ∧
        IsConj g (g32p_literalRepresentative 94) := by
  exact g32p_archive_step_lift _ _ 94 3 g32p_supplierForest_edge_155144
    g32p_supplierForest_actual_144594

def g32p_supplierForest_node_155172 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155172 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155172 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_138308 := by
  decide +kernel

theorem g32p_supplierForest_actual_155172 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155172) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 3 g32p_supplierForest_edge_155172
    g32p_supplierForest_actual_138308

def g32p_supplierForest_node_155196 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155196 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155196 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_133269 := by
  decide +kernel

theorem g32p_supplierForest_actual_155196 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155196) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 3 g32p_supplierForest_edge_155196
    g32p_supplierForest_actual_133269

def g32p_supplierForest_node_155211 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155211 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155211 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_155071 := by
  decide +kernel

theorem g32p_supplierForest_actual_155211 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155211) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 0 g32p_supplierForest_edge_155211
    g32p_supplierForest_actual_155071

def g32p_supplierForest_node_155213 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155213 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155213 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_155247 := by
  decide +kernel

theorem g32p_supplierForest_actual_155213 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155213) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 3 g32p_supplierForest_edge_155213
    g32p_supplierForest_actual_155247

def g32p_supplierForest_node_155226 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155226 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155226 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_134753 := by
  decide +kernel

theorem g32p_supplierForest_actual_155226 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155226) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_155226
    g32p_supplierForest_actual_134753

def g32p_supplierForest_node_155228 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155228 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155228 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_155214 := by
  decide +kernel

theorem g32p_supplierForest_actual_155228 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155228) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 0 g32p_supplierForest_edge_155228
    g32p_supplierForest_actual_155214

def g32p_supplierForest_node_155244 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155244 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155244 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131297 := by
  decide +kernel

theorem g32p_supplierForest_actual_155244 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155244) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_155244
    g32p_supplierForest_actual_131297

def g32p_supplierForest_node_155257 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_155257 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155257 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_143934 := by
  decide +kernel

theorem g32p_supplierForest_actual_155257 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155257) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 1 g32p_supplierForest_edge_155257
    g32p_supplierForest_actual_143934

def g32p_supplierForest_node_155309 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_155309 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155309 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_143510 := by
  decide +kernel

theorem g32p_supplierForest_actual_155309 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155309) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 0 g32p_supplierForest_edge_155309
    g32p_supplierForest_actual_143510

def g32p_supplierForest_node_155318 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155318 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155318 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_140556 := by
  decide +kernel

theorem g32p_supplierForest_actual_155318 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155318) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 3 g32p_supplierForest_edge_155318
    g32p_supplierForest_actual_140556

def g32p_supplierForest_node_155324 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_155324 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155324 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155326 := by
  decide +kernel

theorem g32p_supplierForest_actual_155324 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155324) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 1 g32p_supplierForest_edge_155324
    g32p_supplierForest_actual_155326

def g32p_supplierForest_node_155341 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_155341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155341 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_139011 := by
  decide +kernel

theorem g32p_supplierForest_actual_155341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155341) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_155341
    g32p_supplierForest_actual_139011

def g32p_supplierForest_node_155377 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_155377 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155377 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155063 := by
  decide +kernel

theorem g32p_supplierForest_actual_155377 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155377) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 2 g32p_supplierForest_edge_155377
    g32p_supplierForest_actual_155063

def g32p_supplierForest_node_155382 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155382 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155382 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_142543 := by
  decide +kernel

theorem g32p_supplierForest_actual_155382 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155382) ∧
        IsConj g (g32p_literalRepresentative 94) := by
  exact g32p_archive_step_lift _ _ 94 1 g32p_supplierForest_edge_155382
    g32p_supplierForest_actual_142543

def g32p_supplierForest_node_155412 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_155412 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155412 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_155158 := by
  decide +kernel

theorem g32p_supplierForest_actual_155412 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155412) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 0 g32p_supplierForest_edge_155412
    g32p_supplierForest_actual_155158

def g32p_supplierForest_node_155416 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_155416 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155416 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_155227 := by
  decide +kernel

theorem g32p_supplierForest_actual_155416 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155416) ∧
        IsConj g (g32p_literalRepresentative 76) := by
  exact g32p_archive_step_lift _ _ 76 3 g32p_supplierForest_edge_155416
    g32p_supplierForest_actual_155227

def g32p_supplierForest_node_155419 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155419 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155419 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_143922 := by
  decide +kernel

theorem g32p_supplierForest_actual_155419 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155419) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 3 g32p_supplierForest_edge_155419
    g32p_supplierForest_actual_143922

def g32p_supplierForest_node_155436 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155436 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_144285 := by
  decide +kernel

theorem g32p_supplierForest_actual_155436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155436) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 3 g32p_supplierForest_edge_155436
    g32p_supplierForest_actual_144285

def g32p_supplierForest_node_155440 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155440 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155440 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_144461 := by
  decide +kernel

theorem g32p_supplierForest_actual_155440 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155440) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 1 g32p_supplierForest_edge_155440
    g32p_supplierForest_actual_144461

def g32p_supplierForest_node_155449 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_155449 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155449 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_144278 := by
  decide +kernel

theorem g32p_supplierForest_actual_155449 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155449) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 3 g32p_supplierForest_edge_155449
    g32p_supplierForest_actual_144278

def g32p_supplierForest_node_155451 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_155451 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155451 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_144236 := by
  decide +kernel

theorem g32p_supplierForest_actual_155451 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155451) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 1 g32p_supplierForest_edge_155451
    g32p_supplierForest_actual_144236

def g32p_supplierForest_node_155460 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_155460 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155460 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_155428 := by
  decide +kernel

theorem g32p_supplierForest_actual_155460 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155460) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 0 g32p_supplierForest_edge_155460
    g32p_supplierForest_actual_155428

def g32p_supplierForest_node_155470 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155470 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155470 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155477 := by
  decide +kernel

theorem g32p_supplierForest_actual_155470 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155470) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 1 g32p_supplierForest_edge_155470
    g32p_supplierForest_actual_155477

def g32p_supplierForest_node_155475 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155475 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155475 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155487 := by
  decide +kernel

theorem g32p_supplierForest_actual_155475 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155475) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 1 g32p_supplierForest_edge_155475
    g32p_supplierForest_actual_155487

def g32p_supplierForest_node_155479 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155479 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155479 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_155499 := by
  decide +kernel

theorem g32p_supplierForest_actual_155479 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155479) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 2 g32p_supplierForest_edge_155479
    g32p_supplierForest_actual_155499

def g32p_supplierForest_node_155509 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_155509 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155509 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_155508 := by
  decide +kernel

theorem g32p_supplierForest_actual_155509 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155509) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 1 g32p_supplierForest_edge_155509
    g32p_supplierForest_actual_155508

def g32p_supplierForest_node_155518 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_155518 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_155518 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_155508 := by
  decide +kernel

theorem g32p_supplierForest_actual_155518 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_155518) ∧
        IsConj g (g32p_literalRepresentative 100) := by
  exact g32p_archive_step_lift _ _ 100 3 g32p_supplierForest_edge_155518
    g32p_supplierForest_actual_155508

def g32p_supplierForest_node_000251 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000251 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000251 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_003570 := by
  decide +kernel

theorem g32p_supplierForest_actual_000251 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000251) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_000251
    g32p_supplierForest_actual_003570

def g32p_supplierForest_node_000276 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_000276 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000276 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002578 := by
  decide +kernel

theorem g32p_supplierForest_actual_000276 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000276) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 0 g32p_supplierForest_edge_000276
    g32p_supplierForest_actual_002578

def g32p_supplierForest_node_000318 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000318 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000318 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002684 := by
  decide +kernel

theorem g32p_supplierForest_actual_000318 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000318) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_000318
    g32p_supplierForest_actual_002684

def g32p_supplierForest_node_000331 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000331 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000331 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002714 := by
  decide +kernel

theorem g32p_supplierForest_actual_000331 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000331) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_000331
    g32p_supplierForest_actual_002714

def g32p_supplierForest_node_000376 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000376 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000376 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002810 := by
  decide +kernel

theorem g32p_supplierForest_actual_000376 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000376) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_000376
    g32p_supplierForest_actual_002810

def g32p_supplierForest_node_000459 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000459 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000459 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_006986 := by
  decide +kernel

theorem g32p_supplierForest_actual_000459 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000459) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_000459
    g32p_supplierForest_actual_006986

def g32p_supplierForest_node_000495 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000495 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000495 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000639 := by
  decide +kernel

theorem g32p_supplierForest_actual_000495 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000495) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_000495
    g32p_supplierForest_actual_000639

def g32p_supplierForest_node_000503 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000503 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000503 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_009271 := by
  decide +kernel

theorem g32p_supplierForest_actual_000503 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000503) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 1 g32p_supplierForest_edge_000503
    g32p_supplierForest_actual_009271

def g32p_supplierForest_node_000516 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000516 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000516 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000702 := by
  decide +kernel

theorem g32p_supplierForest_actual_000516 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000516) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_000516
    g32p_supplierForest_actual_000702

def g32p_supplierForest_node_000539 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_000539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000539 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_006675 := by
  decide +kernel

theorem g32p_supplierForest_actual_000539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000539) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_000539
    g32p_supplierForest_actual_006675

def g32p_supplierForest_node_000569 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000569 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_008248 := by
  decide +kernel

theorem g32p_supplierForest_actual_000569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000569) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 3 g32p_supplierForest_edge_000569
    g32p_supplierForest_actual_008248

def g32p_supplierForest_node_000609 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000609 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000609 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010787 := by
  decide +kernel

theorem g32p_supplierForest_actual_000609 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000609) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_000609
    g32p_supplierForest_actual_010787

def g32p_supplierForest_node_000629 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000629 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000629 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000029 := by
  decide +kernel

theorem g32p_supplierForest_actual_000629 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000629) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 2 g32p_supplierForest_edge_000629
    g32p_supplierForest_actual_000029

def g32p_supplierForest_node_000654 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000654 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000654 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001029 := by
  decide +kernel

theorem g32p_supplierForest_actual_000654 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000654) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_000654
    g32p_supplierForest_actual_001029

def g32p_supplierForest_node_000687 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000687 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000687 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005799 := by
  decide +kernel

theorem g32p_supplierForest_actual_000687 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000687) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_000687
    g32p_supplierForest_actual_005799

def g32p_supplierForest_node_000772 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_000772 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000772 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_005993 := by
  decide +kernel

theorem g32p_supplierForest_actual_000772 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000772) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_000772
    g32p_supplierForest_actual_005993

def g32p_supplierForest_node_000791 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000791 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000791 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_011138 := by
  decide +kernel

theorem g32p_supplierForest_actual_000791 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000791) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 2 g32p_supplierForest_edge_000791
    g32p_supplierForest_actual_011138

def g32p_supplierForest_node_000803 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000803 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000803 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_008340 := by
  decide +kernel

theorem g32p_supplierForest_actual_000803 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000803) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 3 g32p_supplierForest_edge_000803
    g32p_supplierForest_actual_008340

def g32p_supplierForest_node_000806 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000806 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000806 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000828 := by
  decide +kernel

theorem g32p_supplierForest_actual_000806 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000806) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_000806
    g32p_supplierForest_actual_000828

def g32p_supplierForest_node_000821 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000821 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000821 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_006102 := by
  decide +kernel

theorem g32p_supplierForest_actual_000821 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000821) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_000821
    g32p_supplierForest_actual_006102

def g32p_supplierForest_node_000823 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000823 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000823 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_000038 := by
  decide +kernel

theorem g32p_supplierForest_actual_000823 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000823) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_000823
    g32p_supplierForest_actual_000038

def g32p_supplierForest_node_000834 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_000834 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000834 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000974 := by
  decide +kernel

theorem g32p_supplierForest_actual_000834 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000834) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 1 g32p_supplierForest_edge_000834
    g32p_supplierForest_actual_000974

def g32p_supplierForest_node_000885 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000885 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000885 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_000469 := by
  decide +kernel

theorem g32p_supplierForest_actual_000885 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000885) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_000885
    g32p_supplierForest_actual_000469

def g32p_supplierForest_node_000886 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000886 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000886 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_000722 := by
  decide +kernel

theorem g32p_supplierForest_actual_000886 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000886) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 2 g32p_supplierForest_edge_000886
    g32p_supplierForest_actual_000722

def g32p_supplierForest_node_000912 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_000912 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000912 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_000761 := by
  decide +kernel

theorem g32p_supplierForest_actual_000912 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000912) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_000912
    g32p_supplierForest_actual_000761

def g32p_supplierForest_node_000954 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_000954 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000954 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_009575 := by
  decide +kernel

theorem g32p_supplierForest_actual_000954 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000954) ∧
        IsConj g (g32p_literalRepresentative 18) := by
  exact g32p_archive_step_lift _ _ 18 1 g32p_supplierForest_edge_000954
    g32p_supplierForest_actual_009575

def g32p_supplierForest_node_000962 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_000962 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000962 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011392 := by
  decide +kernel

theorem g32p_supplierForest_actual_000962 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000962) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_000962
    g32p_supplierForest_actual_011392

def g32p_supplierForest_node_000971 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_000971 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_000971 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011443 := by
  decide +kernel

theorem g32p_supplierForest_actual_000971 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_000971) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_000971
    g32p_supplierForest_actual_011443

def g32p_supplierForest_node_001027 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_001027 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001027 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_006569 := by
  decide +kernel

theorem g32p_supplierForest_actual_001027 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001027) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_001027
    g32p_supplierForest_actual_006569

def g32p_supplierForest_node_001028 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001028 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001028 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_006572 := by
  decide +kernel

theorem g32p_supplierForest_actual_001028 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001028) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 0 g32p_supplierForest_edge_001028
    g32p_supplierForest_actual_006572

def g32p_supplierForest_node_001088 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001088 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001088 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012491 := by
  decide +kernel

theorem g32p_supplierForest_actual_001088 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001088) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001088
    g32p_supplierForest_actual_012491

def g32p_supplierForest_node_001097 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001097 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001097 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001295 := by
  decide +kernel

theorem g32p_supplierForest_actual_001097 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001097) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001097
    g32p_supplierForest_actual_001295

def g32p_supplierForest_node_001106 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001106 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001106 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001322 := by
  decide +kernel

theorem g32p_supplierForest_actual_001106 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001106) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001106
    g32p_supplierForest_actual_001322

def g32p_supplierForest_node_001188 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001188 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001188 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001508 := by
  decide +kernel

theorem g32p_supplierForest_actual_001188 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001188) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001188
    g32p_supplierForest_actual_001508

def g32p_supplierForest_node_001221 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001221 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001221 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001425 := by
  decide +kernel

theorem g32p_supplierForest_actual_001221 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001221) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001221
    g32p_supplierForest_actual_001425

def g32p_supplierForest_node_001227 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_001227 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001227 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014063 := by
  decide +kernel

theorem g32p_supplierForest_actual_001227 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001227) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001227
    g32p_supplierForest_actual_014063

def g32p_supplierForest_node_001240 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001240 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001240 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001444 := by
  decide +kernel

theorem g32p_supplierForest_actual_001240 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001240) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001240
    g32p_supplierForest_actual_001444

def g32p_supplierForest_node_001260 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_001260 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001260 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001682 := by
  decide +kernel

theorem g32p_supplierForest_actual_001260 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001260) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001260
    g32p_supplierForest_actual_001682

def g32p_supplierForest_node_001303 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001303 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001303 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_016740 := by
  decide +kernel

theorem g32p_supplierForest_actual_001303 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001303) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_001303
    g32p_supplierForest_actual_016740

def g32p_supplierForest_node_001316 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_001316 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001316 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015187 := by
  decide +kernel

theorem g32p_supplierForest_actual_001316 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001316) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_001316
    g32p_supplierForest_actual_015187

def g32p_supplierForest_node_001403 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001403 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001403 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016040 := by
  decide +kernel

theorem g32p_supplierForest_actual_001403 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001403) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001403
    g32p_supplierForest_actual_016040

def g32p_supplierForest_node_001430 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001430 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001430 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014457 := by
  decide +kernel

theorem g32p_supplierForest_actual_001430 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001430) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001430
    g32p_supplierForest_actual_014457

def g32p_supplierForest_node_001431 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001431 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001431 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016039 := by
  decide +kernel

theorem g32p_supplierForest_actual_001431 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001431) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001431
    g32p_supplierForest_actual_016039

def g32p_supplierForest_node_001434 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001434 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001434 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016847 := by
  decide +kernel

theorem g32p_supplierForest_actual_001434 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001434) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001434
    g32p_supplierForest_actual_016847

def g32p_supplierForest_node_001445 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001445 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_014485 := by
  decide +kernel

theorem g32p_supplierForest_actual_001445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001445) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001445
    g32p_supplierForest_actual_014485

def g32p_supplierForest_node_001451 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_001451 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001451 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024364 := by
  decide +kernel

theorem g32p_supplierForest_actual_001451 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001451) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001451
    g32p_supplierForest_actual_024364

def g32p_supplierForest_node_001467 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_001467 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001467 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_001322 := by
  decide +kernel

theorem g32p_supplierForest_actual_001467 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001467) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_001467
    g32p_supplierForest_actual_001322

def g32p_supplierForest_node_001517 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001517 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001517 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001810 := by
  decide +kernel

theorem g32p_supplierForest_actual_001517 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001517) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_001517
    g32p_supplierForest_actual_001810

def g32p_supplierForest_node_001545 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001545 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001545 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002329 := by
  decide +kernel

theorem g32p_supplierForest_actual_001545 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001545) ∧
        IsConj g (g32p_literalRepresentative 28) := by
  exact g32p_archive_step_lift _ _ 28 0 g32p_supplierForest_edge_001545
    g32p_supplierForest_actual_002329

def g32p_supplierForest_node_001565 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_001565 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001565 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002373 := by
  decide +kernel

theorem g32p_supplierForest_actual_001565 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001565) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_001565
    g32p_supplierForest_actual_002373

def g32p_supplierForest_node_001575 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001575 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001575 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002396 := by
  decide +kernel

theorem g32p_supplierForest_actual_001575 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001575) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001575
    g32p_supplierForest_actual_002396

def g32p_supplierForest_node_001583 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001583 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001583 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_019444 := by
  decide +kernel

theorem g32p_supplierForest_actual_001583 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001583) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001583
    g32p_supplierForest_actual_019444

def g32p_supplierForest_node_001678 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001678 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001678 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012375 := by
  decide +kernel

theorem g32p_supplierForest_actual_001678 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001678) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001678
    g32p_supplierForest_actual_012375

def g32p_supplierForest_node_001705 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001705 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001705 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001165 := by
  decide +kernel

theorem g32p_supplierForest_actual_001705 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001705) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001705
    g32p_supplierForest_actual_001165

def g32p_supplierForest_node_001723 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001723 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001723 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001508 := by
  decide +kernel

theorem g32p_supplierForest_actual_001723 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001723) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001723
    g32p_supplierForest_actual_001508

def g32p_supplierForest_node_001727 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001727 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001727 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012492 := by
  decide +kernel

theorem g32p_supplierForest_actual_001727 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001727) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_001727
    g32p_supplierForest_actual_012492

def g32p_supplierForest_node_001733 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001733 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001733 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018668 := by
  decide +kernel

theorem g32p_supplierForest_actual_001733 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001733) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001733
    g32p_supplierForest_actual_018668

def g32p_supplierForest_node_001740 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001740 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001740 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001543 := by
  decide +kernel

theorem g32p_supplierForest_actual_001740 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001740) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001740
    g32p_supplierForest_actual_001543

def g32p_supplierForest_node_001743 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001743 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001743 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001092 := by
  decide +kernel

theorem g32p_supplierForest_actual_001743 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001743) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 0 g32p_supplierForest_edge_001743
    g32p_supplierForest_actual_001092

def g32p_supplierForest_node_001756 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_001756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001756 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_001091 := by
  decide +kernel

theorem g32p_supplierForest_actual_001756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001756) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_001756
    g32p_supplierForest_actual_001091

def g32p_supplierForest_node_001782 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001782 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001782 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012618 := by
  decide +kernel

theorem g32p_supplierForest_actual_001782 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001782) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001782
    g32p_supplierForest_actual_012618

def g32p_supplierForest_node_001827 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001827 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001827 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012698 := by
  decide +kernel

theorem g32p_supplierForest_actual_001827 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001827) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_001827
    g32p_supplierForest_actual_012698

def g32p_supplierForest_node_001883 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001883 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001883 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002030 := by
  decide +kernel

theorem g32p_supplierForest_actual_001883 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001883) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001883
    g32p_supplierForest_actual_002030

def g32p_supplierForest_node_001920 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_001920 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001920 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002105 := by
  decide +kernel

theorem g32p_supplierForest_actual_001920 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001920) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_001920
    g32p_supplierForest_actual_002105

def g32p_supplierForest_node_001952 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_001952 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_001952 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012979 := by
  decide +kernel

theorem g32p_supplierForest_actual_001952 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_001952) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 0 g32p_supplierForest_edge_001952
    g32p_supplierForest_actual_012979

def g32p_supplierForest_node_002058 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002058 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002058 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001332 := by
  decide +kernel

theorem g32p_supplierForest_actual_002058 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002058) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_002058
    g32p_supplierForest_actual_001332

def g32p_supplierForest_node_002080 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002080 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002080 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002396 := by
  decide +kernel

theorem g32p_supplierForest_actual_002080 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002080) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_002080
    g32p_supplierForest_actual_002396

def g32p_supplierForest_node_002102 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002102 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002102 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_013307 := by
  decide +kernel

theorem g32p_supplierForest_actual_002102 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002102) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_002102
    g32p_supplierForest_actual_013307

def g32p_supplierForest_node_002140 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002140 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002140 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001165 := by
  decide +kernel

theorem g32p_supplierForest_actual_002140 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002140) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_002140
    g32p_supplierForest_actual_001165

def g32p_supplierForest_node_002169 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_002169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002169 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_001197 := by
  decide +kernel

theorem g32p_supplierForest_actual_002169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002169) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_002169
    g32p_supplierForest_actual_001197

def g32p_supplierForest_node_002225 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002225 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002225 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002129 := by
  decide +kernel

theorem g32p_supplierForest_actual_002225 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002225) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_002225
    g32p_supplierForest_actual_002129

def g32p_supplierForest_node_002254 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_002254 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002254 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_013633 := by
  decide +kernel

theorem g32p_supplierForest_actual_002254 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002254) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_002254
    g32p_supplierForest_actual_013633

def g32p_supplierForest_node_002297 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_002297 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002297 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_001872 := by
  decide +kernel

theorem g32p_supplierForest_actual_002297 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002297) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_002297
    g32p_supplierForest_actual_001872

def g32p_supplierForest_node_002302 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_002302 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002302 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002393 := by
  decide +kernel

theorem g32p_supplierForest_actual_002302 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002302) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_002302
    g32p_supplierForest_actual_002393

def g32p_supplierForest_node_002366 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_002366 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002366 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_013860 := by
  decide +kernel

theorem g32p_supplierForest_actual_002366 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002366) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_002366
    g32p_supplierForest_actual_013860

def g32p_supplierForest_node_002376 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_002376 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002376 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_002294 := by
  decide +kernel

theorem g32p_supplierForest_actual_002376 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002376) ∧
        IsConj g (g32p_literalRepresentative 8) := by
  exact g32p_archive_step_lift _ _ 8 3 g32p_supplierForest_edge_002376
    g32p_supplierForest_actual_002294

def g32p_supplierForest_node_002395 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002395 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002395 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_013925 := by
  decide +kernel

theorem g32p_supplierForest_actual_002395 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002395) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_002395
    g32p_supplierForest_actual_013925

def g32p_supplierForest_node_002479 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_002479 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002479 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_014389 := by
  decide +kernel

theorem g32p_supplierForest_actual_002479 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002479) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 2 g32p_supplierForest_edge_002479
    g32p_supplierForest_actual_014389

def g32p_supplierForest_node_002588 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_002588 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002588 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003182 := by
  decide +kernel

theorem g32p_supplierForest_actual_002588 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002588) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 1 g32p_supplierForest_edge_002588
    g32p_supplierForest_actual_003182

def g32p_supplierForest_node_002621 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002621 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_002636 := by
  decide +kernel

theorem g32p_supplierForest_actual_002621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002621) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_002621
    g32p_supplierForest_actual_002636

def g32p_supplierForest_node_002648 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002648 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002648 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003184 := by
  decide +kernel

theorem g32p_supplierForest_actual_002648 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002648) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 0 g32p_supplierForest_edge_002648
    g32p_supplierForest_actual_003184

def g32p_supplierForest_node_002661 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002661 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002661 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025171 := by
  decide +kernel

theorem g32p_supplierForest_actual_002661 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002661) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 1 g32p_supplierForest_edge_002661
    g32p_supplierForest_actual_025171

def g32p_supplierForest_node_002689 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002689 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002689 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_003278 := by
  decide +kernel

theorem g32p_supplierForest_actual_002689 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002689) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 0 g32p_supplierForest_edge_002689
    g32p_supplierForest_actual_003278

def g32p_supplierForest_node_002693 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002693 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002693 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_029415 := by
  decide +kernel

theorem g32p_supplierForest_actual_002693 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002693) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_002693
    g32p_supplierForest_actual_029415

def g32p_supplierForest_node_002727 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_002727 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002727 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_029466 := by
  decide +kernel

theorem g32p_supplierForest_actual_002727 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002727) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_002727
    g32p_supplierForest_actual_029466

def g32p_supplierForest_node_002800 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_002800 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002800 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_002756 := by
  decide +kernel

theorem g32p_supplierForest_actual_002800 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002800) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 2 g32p_supplierForest_edge_002800
    g32p_supplierForest_actual_002756

def g32p_supplierForest_node_002866 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_002866 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002866 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_036700 := by
  decide +kernel

theorem g32p_supplierForest_actual_002866 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002866) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_002866
    g32p_supplierForest_actual_036700

def g32p_supplierForest_node_002887 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002887 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002887 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_004461 := by
  decide +kernel

theorem g32p_supplierForest_actual_002887 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002887) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 1 g32p_supplierForest_edge_002887
    g32p_supplierForest_actual_004461

def g32p_supplierForest_node_002977 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_002977 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002977 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003031 := by
  decide +kernel

theorem g32p_supplierForest_actual_002977 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002977) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 1 g32p_supplierForest_edge_002977
    g32p_supplierForest_actual_003031

def g32p_supplierForest_node_002983 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_002983 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002983 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_037042 := by
  decide +kernel

theorem g32p_supplierForest_actual_002983 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002983) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 3 g32p_supplierForest_edge_002983
    g32p_supplierForest_actual_037042

def g32p_supplierForest_node_002986 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_002986 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_002986 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032651 := by
  decide +kernel

theorem g32p_supplierForest_actual_002986 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_002986) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 2 g32p_supplierForest_edge_002986
    g32p_supplierForest_actual_032651

def g32p_supplierForest_node_003002 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_003002 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003002 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003085 := by
  decide +kernel

theorem g32p_supplierForest_actual_003002 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003002) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_003002
    g32p_supplierForest_actual_003085

def g32p_supplierForest_node_003033 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_003033 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003033 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003300 := by
  decide +kernel

theorem g32p_supplierForest_actual_003033 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003033) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_003033
    g32p_supplierForest_actual_003300

def g32p_supplierForest_node_003039 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_003039 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003039 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029143 := by
  decide +kernel

theorem g32p_supplierForest_actual_003039 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003039) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_003039
    g32p_supplierForest_actual_029143

def g32p_supplierForest_node_003040 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003040 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003319 := by
  decide +kernel

theorem g32p_supplierForest_actual_003040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003040) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 1 g32p_supplierForest_edge_003040
    g32p_supplierForest_actual_003319

def g32p_supplierForest_node_003050 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_003050 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003050 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032659 := by
  decide +kernel

theorem g32p_supplierForest_actual_003050 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003050) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 2 g32p_supplierForest_edge_003050
    g32p_supplierForest_actual_032659

def g32p_supplierForest_node_003082 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_003082 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003082 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036152 := by
  decide +kernel

theorem g32p_supplierForest_actual_003082 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003082) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 3 g32p_supplierForest_edge_003082
    g32p_supplierForest_actual_036152

def g32p_supplierForest_node_003098 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_003098 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003098 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_003882 := by
  decide +kernel

theorem g32p_supplierForest_actual_003098 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003098) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_003098
    g32p_supplierForest_actual_003882

def g32p_supplierForest_node_003108 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_003108 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003108 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_024507 := by
  decide +kernel

theorem g32p_supplierForest_actual_003108 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003108) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_003108
    g32p_supplierForest_actual_024507

def g32p_supplierForest_node_003126 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_003126 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_003126 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_002990 := by
  decide +kernel

theorem g32p_supplierForest_actual_003126 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_003126) ∧
        IsConj g (g32p_literalRepresentative 31) := by
  exact g32p_archive_step_lift _ _ 31 0 g32p_supplierForest_edge_003126
    g32p_supplierForest_actual_002990

end HodgeLean.Foundations.Program

end
end
