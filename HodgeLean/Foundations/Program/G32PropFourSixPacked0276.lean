import HodgeLean.Foundations.Program.G32PropFourSixPacked0272
import HodgeLean.Foundations.Program.G32PropFourSixPacked0273
import HodgeLean.Foundations.Program.G32PropFourSixPacked0274
import HodgeLean.Foundations.Program.G32PropFourSixPacked0275
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0257
import HodgeLean.Foundations.Program.G32PropFourSixPacked0258
import HodgeLean.Foundations.Program.G32PropFourSixPacked0260
import HodgeLean.Foundations.Program.G32PropFourSixPacked0261
import HodgeLean.Foundations.Program.G32PropFourSixPacked0262
import HodgeLean.Foundations.Program.G32PropFourSixPacked0263
import HodgeLean.Foundations.Program.G32PropFourSixPacked0264
import HodgeLean.Foundations.Program.G32PropFourSixPacked0265
import HodgeLean.Foundations.Program.G32PropFourSixPacked0269
import HodgeLean.Foundations.Program.G32PropFourSixPacked0270
import HodgeLean.Foundations.Program.G32PropFourSixPacked0271

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_112 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_000832 else g32p_supplierForest_node_000986) else (if i.val < 3 then g32p_supplierForest_node_001144 else g32p_supplierForest_node_001205)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_001259 else g32p_supplierForest_node_001351) else (if i.val < 7 then g32p_supplierForest_node_001372 else g32p_supplierForest_node_001414))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_001514 else g32p_supplierForest_node_001615) else (if i.val < 11 then g32p_supplierForest_node_001634 else g32p_supplierForest_node_001732)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_001966 else g32p_supplierForest_node_001982) else (if i.val < 15 then g32p_supplierForest_node_002014 else g32p_supplierForest_node_002050)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_002084 else g32p_supplierForest_node_002113) else (if i.val < 19 then g32p_supplierForest_node_002186 else g32p_supplierForest_node_002208)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_002221 else g32p_supplierForest_node_002325) else (if i.val < 23 then g32p_supplierForest_node_002337 else g32p_supplierForest_node_002344))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_002353 else g32p_supplierForest_node_002357) else (if i.val < 27 then g32p_supplierForest_node_002368 else g32p_supplierForest_node_002429)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_002518 else g32p_supplierForest_node_002527) else (if i.val < 31 then g32p_supplierForest_node_002604 else g32p_supplierForest_node_002607))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_002628 else g32p_supplierForest_node_002641) else (if i.val < 35 then g32p_supplierForest_node_002674 else g32p_supplierForest_node_002723)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_002770 else g32p_supplierForest_node_002811) else (if i.val < 39 then g32p_supplierForest_node_002886 else g32p_supplierForest_node_002961))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_002962 else g32p_supplierForest_node_003062) else (if i.val < 43 then g32p_supplierForest_node_003131 else g32p_supplierForest_node_003181)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_003246 else g32p_supplierForest_node_003251) else (if i.val < 47 then g32p_supplierForest_node_003280 else g32p_supplierForest_node_003282)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_003316 else g32p_supplierForest_node_003321) else (if i.val < 51 then g32p_supplierForest_node_003408 else g32p_supplierForest_node_003461)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_003492 else g32p_supplierForest_node_003510) else (if i.val < 55 then g32p_supplierForest_node_003532 else g32p_supplierForest_node_003536))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_003541 else g32p_supplierForest_node_003606) else (if i.val < 59 then g32p_supplierForest_node_003672 else g32p_supplierForest_node_003694)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_003744 else g32p_supplierForest_node_003799) else (if i.val < 63 then g32p_supplierForest_node_003800 else g32p_supplierForest_node_003980)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_004180 else g32p_supplierForest_node_004212) else (if i.val < 67 then g32p_supplierForest_node_004242 else g32p_supplierForest_node_004256)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_004321 else g32p_supplierForest_node_004482) else (if i.val < 71 then g32p_supplierForest_node_004546 else g32p_supplierForest_node_004693))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_004696 else g32p_supplierForest_node_004701) else (if i.val < 75 then g32p_supplierForest_node_004729 else g32p_supplierForest_node_004808)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_004814 else g32p_supplierForest_node_004817) else (if i.val < 79 then g32p_supplierForest_node_004936 else g32p_supplierForest_node_004966)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_005025 else g32p_supplierForest_node_005060) else (if i.val < 83 then g32p_supplierForest_node_005070 else g32p_supplierForest_node_005092)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_005094 else g32p_supplierForest_node_005100) else (if i.val < 87 then g32p_supplierForest_node_005138 else g32p_supplierForest_node_005146))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_005235 else g32p_supplierForest_node_005256) else (if i.val < 91 then g32p_supplierForest_node_005280 else g32p_supplierForest_node_005284)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_005327 else g32p_supplierForest_node_005331) else (if i.val < 95 then g32p_supplierForest_node_005345 else g32p_supplierForest_node_005352))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_005355 else g32p_supplierForest_node_005375) else (if i.val < 99 then g32p_supplierForest_node_005465 else g32p_supplierForest_node_005475)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_005480 else g32p_supplierForest_node_005543) else (if i.val < 103 then g32p_supplierForest_node_005549 else g32p_supplierForest_node_005565))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_005706 else g32p_supplierForest_node_005707) else (if i.val < 107 then g32p_supplierForest_node_005837 else g32p_supplierForest_node_005846)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_006020 else g32p_supplierForest_node_006039) else (if i.val < 111 then g32p_supplierForest_node_006063 else g32p_supplierForest_node_006094)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_006097 else g32p_supplierForest_node_006141) else (if i.val < 115 then g32p_supplierForest_node_006171 else g32p_supplierForest_node_006175)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_006185 else g32p_supplierForest_node_006210) else (if i.val < 119 then g32p_supplierForest_node_006223 else g32p_supplierForest_node_006269))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_006367 else g32p_supplierForest_node_006391) else (if i.val < 123 then g32p_supplierForest_node_006423 else g32p_supplierForest_node_006438)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_006503 else g32p_supplierForest_node_006537) else (if i.val < 127 then g32p_supplierForest_node_006538 else g32p_supplierForest_node_006558))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_006574 else g32p_supplierForest_node_006590) else (if i.val < 131 then g32p_supplierForest_node_006593 else g32p_supplierForest_node_006641)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_006667 else g32p_supplierForest_node_006754) else (if i.val < 135 then g32p_supplierForest_node_006764 else g32p_supplierForest_node_006788))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_006822 else g32p_supplierForest_node_006837) else (if i.val < 139 then g32p_supplierForest_node_006847 else g32p_supplierForest_node_006884)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_006925 else g32p_supplierForest_node_007040) else (if i.val < 143 then g32p_supplierForest_node_007148 else g32p_supplierForest_node_007249)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_007262 else g32p_supplierForest_node_007289) else (if i.val < 147 then g32p_supplierForest_node_007302 else g32p_supplierForest_node_007336)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_007350 else g32p_supplierForest_node_007431) else (if i.val < 151 then g32p_supplierForest_node_007440 else g32p_supplierForest_node_007538))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_007623 else g32p_supplierForest_node_007634) else (if i.val < 155 then g32p_supplierForest_node_007644 else g32p_supplierForest_node_007668)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_007691 else g32p_supplierForest_node_007709) else (if i.val < 159 then g32p_supplierForest_node_007726 else g32p_supplierForest_node_007803))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_007822 else g32p_supplierForest_node_007828) else (if i.val < 163 then g32p_supplierForest_node_007832 else g32p_supplierForest_node_007837)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_007845 else g32p_supplierForest_node_007884) else (if i.val < 167 then g32p_supplierForest_node_007885 else g32p_supplierForest_node_007974))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_007976 else g32p_supplierForest_node_007994) else (if i.val < 171 then g32p_supplierForest_node_007996 else g32p_supplierForest_node_008034)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_008096 else g32p_supplierForest_node_008127) else (if i.val < 175 then g32p_supplierForest_node_008166 else g32p_supplierForest_node_008198)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_008252 else g32p_supplierForest_node_008262) else (if i.val < 179 then g32p_supplierForest_node_008294 else g32p_supplierForest_node_008307)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_008424 else g32p_supplierForest_node_008440) else (if i.val < 183 then g32p_supplierForest_node_008466 else g32p_supplierForest_node_008482))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_008534 else g32p_supplierForest_node_008548) else (if i.val < 187 then g32p_supplierForest_node_008578 else g32p_supplierForest_node_008583)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_008621 else g32p_supplierForest_node_008628) else (if i.val < 191 then g32p_supplierForest_node_008645 else g32p_supplierForest_node_008681)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_008775 else g32p_supplierForest_node_008779) else (if i.val < 195 then g32p_supplierForest_node_008805 else g32p_supplierForest_node_008814)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_008816 else g32p_supplierForest_node_008873) else (if i.val < 199 then g32p_supplierForest_node_008890 else g32p_supplierForest_node_008894))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_008898 else g32p_supplierForest_node_008940) else (if i.val < 203 then g32p_supplierForest_node_008942 else g32p_supplierForest_node_008971)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_008996 else g32p_supplierForest_node_009041) else (if i.val < 207 then g32p_supplierForest_node_009092 else g32p_supplierForest_node_009205)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_009213 else g32p_supplierForest_node_009226) else (if i.val < 211 then g32p_supplierForest_node_009419 else g32p_supplierForest_node_009432)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_009444 else g32p_supplierForest_node_009471) else (if i.val < 215 then g32p_supplierForest_node_009520 else g32p_supplierForest_node_009523))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_009583 else g32p_supplierForest_node_009586) else (if i.val < 219 then g32p_supplierForest_node_009611 else g32p_supplierForest_node_009618)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_009667 else g32p_supplierForest_node_009718) else (if i.val < 223 then g32p_supplierForest_node_009728 else g32p_supplierForest_node_009734))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_009742 else g32p_supplierForest_node_009758) else (if i.val < 227 then g32p_supplierForest_node_009761 else g32p_supplierForest_node_009801)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_009812 else g32p_supplierForest_node_009817) else (if i.val < 231 then g32p_supplierForest_node_009818 else g32p_supplierForest_node_009841))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_009953 else g32p_supplierForest_node_010059) else (if i.val < 235 then g32p_supplierForest_node_010113 else g32p_supplierForest_node_010134)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_010147 else g32p_supplierForest_node_010206) else (if i.val < 239 then g32p_supplierForest_node_010272 else g32p_supplierForest_node_010299)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_010350 else g32p_supplierForest_node_010399) else (if i.val < 243 then g32p_supplierForest_node_010414 else g32p_supplierForest_node_010486)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_010555 else g32p_supplierForest_node_010608) else (if i.val < 247 then g32p_supplierForest_node_010619 else g32p_supplierForest_node_010641))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_010708 else g32p_supplierForest_node_010713) else (if i.val < 251 then g32p_supplierForest_node_010740 else g32p_supplierForest_node_010743)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_010794 else g32p_supplierForest_node_010808) else (if i.val < 255 then g32p_supplierForest_node_010831 else g32p_supplierForest_node_010888))))))))

def g32p_supplierForest_classes_112 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 22 else 21) else (if i.val < 3 then 25 else 10)) else (if i.val < 6 then (if i.val < 5 then 10 else 25) else (if i.val < 7 then 10 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9 else 26) else (if i.val < 11 then 26 else 10)) else (if i.val < 14 then (if i.val < 13 then 10 else 10) else (if i.val < 15 then 10 else 10)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 9) else (if i.val < 19 then 9 else 25)) else (if i.val < 22 then (if i.val < 21 then 27 else 10) else (if i.val < 23 then 25 else 10))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 10 else 26) else (if i.val < 27 then 10 else 10)) else (if i.val < 30 then (if i.val < 29 then 10 else 27) else (if i.val < 31 then 29 else 14))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 14 else 15) else (if i.val < 35 then 4 else 30)) else (if i.val < 38 then (if i.val < 37 then 14 else 4) else (if i.val < 39 then 29 else 17))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 16 else 30) else (if i.val < 43 then 30 else 16)) else (if i.val < 46 then (if i.val < 45 then 16 else 17) else (if i.val < 47 then 14 else 16)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 16 else 30) else (if i.val < 51 then 16 else 15)) else (if i.val < 54 then (if i.val < 53 then 4 else 32) else (if i.val < 55 then 14 else 15))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 17 else 14) else (if i.val < 59 then 35 else 16)) else (if i.val < 62 then (if i.val < 61 then 30 else 30) else (if i.val < 63 then 14 else 17)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 15 else 15) else (if i.val < 67 then 16 else 17)) else (if i.val < 70 then (if i.val < 69 then 15 else 17) else (if i.val < 71 then 17 else 30))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 14 else 15) else (if i.val < 75 then 16 else 15)) else (if i.val < 78 then (if i.val < 77 then 35 else 15) else (if i.val < 79 then 30 else 16)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 16 else 30) else (if i.val < 83 then 17 else 15)) else (if i.val < 86 then (if i.val < 85 then 14 else 17) else (if i.val < 87 then 14 else 17))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 15 else 30) else (if i.val < 91 then 15 else 17)) else (if i.val < 94 then (if i.val < 93 then 30 else 30) else (if i.val < 95 then 17 else 15))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 29 else 14) else (if i.val < 99 then 16 else 29)) else (if i.val < 102 then (if i.val < 101 then 15 else 30) else (if i.val < 103 then 30 else 16))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 16 else 14) else (if i.val < 107 then 40 else 40)) else (if i.val < 110 then (if i.val < 109 then 22 else 22) else (if i.val < 111 then 6 else 7)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 6 else 22) else (if i.val < 115 then 38 else 38)) else (if i.val < 118 then (if i.val < 117 then 38 else 21) else (if i.val < 119 then 21 else 21))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 38 else 7) else (if i.val < 123 then 22 else 22)) else (if i.val < 126 then (if i.val < 125 then 38 else 21) else (if i.val < 127 then 38 else 21))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 22 else 22) else (if i.val < 131 then 22 else 21)) else (if i.val < 134 then (if i.val < 133 then 20 else 21) else (if i.val < 135 then 22 else 40))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 40 else 21) else (if i.val < 139 then 38 else 21)) else (if i.val < 142 then (if i.val < 141 then 38 else 38) else (if i.val < 143 then 22 else 21)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 21 else 40) else (if i.val < 147 then 7 else 21)) else (if i.val < 150 then (if i.val < 149 then 40 else 38) else (if i.val < 151 then 6 else 39))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 21 else 43) else (if i.val < 155 then 21 else 22)) else (if i.val < 158 then (if i.val < 157 then 38 else 40) else (if i.val < 159 then 22 else 6))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 21 else 21) else (if i.val < 163 then 21 else 7)) else (if i.val < 166 then (if i.val < 165 then 40 else 6) else (if i.val < 167 then 39 else 39))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 7 else 7) else (if i.val < 171 then 38 else 21)) else (if i.val < 174 then (if i.val < 173 then 22 else 38) else (if i.val < 175 then 38 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 38 else 6) else (if i.val < 179 then 22 else 38)) else (if i.val < 182 then (if i.val < 181 then 38 else 22) else (if i.val < 183 then 22 else 40))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 38 else 20) else (if i.val < 187 then 38 else 22)) else (if i.val < 190 then (if i.val < 189 then 38 else 22) else (if i.val < 191 then 40 else 22)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 7 else 38) else (if i.val < 195 then 39 else 38)) else (if i.val < 198 then (if i.val < 197 then 23 else 38) else (if i.val < 199 then 22 else 38))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 40 else 22) else (if i.val < 203 then 21 else 20)) else (if i.val < 206 then (if i.val < 205 then 38 else 40) else (if i.val < 207 then 39 else 38)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 21 else 20) else (if i.val < 211 then 22 else 20)) else (if i.val < 214 then (if i.val < 213 then 41 else 22) else (if i.val < 215 then 39 else 22))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 5 else 38) else (if i.val < 219 then 38 else 22)) else (if i.val < 222 then (if i.val < 221 then 22 else 21) else (if i.val < 223 then 21 else 5))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 7 else 21) else (if i.val < 227 then 22 else 38)) else (if i.val < 230 then (if i.val < 229 then 40 else 40) else (if i.val < 231 then 38 else 22))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 22 else 38) else (if i.val < 235 then 21 else 21)) else (if i.val < 238 then (if i.val < 237 then 38 else 7) else (if i.val < 239 then 21 else 38)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 38 else 40) else (if i.val < 243 then 38 else 38)) else (if i.val < 246 then (if i.val < 245 then 22 else 7) else (if i.val < 247 then 20 else 22))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 38 else 21) else (if i.val < 251 then 7 else 7)) else (if i.val < 254 then (if i.val < 253 then 38 else 38) else (if i.val < 255 then 20 else 6))))))))

theorem g32p_supplierForest_actual_112 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_112 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_112 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_000832
  · exact g32p_supplierForest_actual_000986
  · exact g32p_supplierForest_actual_001144
  · exact g32p_supplierForest_actual_001205
  · exact g32p_supplierForest_actual_001259
  · exact g32p_supplierForest_actual_001351
  · exact g32p_supplierForest_actual_001372
  · exact g32p_supplierForest_actual_001414
  · exact g32p_supplierForest_actual_001514
  · exact g32p_supplierForest_actual_001615
  · exact g32p_supplierForest_actual_001634
  · exact g32p_supplierForest_actual_001732
  · exact g32p_supplierForest_actual_001966
  · exact g32p_supplierForest_actual_001982
  · exact g32p_supplierForest_actual_002014
  · exact g32p_supplierForest_actual_002050
  · exact g32p_supplierForest_actual_002084
  · exact g32p_supplierForest_actual_002113
  · exact g32p_supplierForest_actual_002186
  · exact g32p_supplierForest_actual_002208
  · exact g32p_supplierForest_actual_002221
  · exact g32p_supplierForest_actual_002325
  · exact g32p_supplierForest_actual_002337
  · exact g32p_supplierForest_actual_002344
  · exact g32p_supplierForest_actual_002353
  · exact g32p_supplierForest_actual_002357
  · exact g32p_supplierForest_actual_002368
  · exact g32p_supplierForest_actual_002429
  · exact g32p_supplierForest_actual_002518
  · exact g32p_supplierForest_actual_002527
  · exact g32p_supplierForest_actual_002604
  · exact g32p_supplierForest_actual_002607
  · exact g32p_supplierForest_actual_002628
  · exact g32p_supplierForest_actual_002641
  · exact g32p_supplierForest_actual_002674
  · exact g32p_supplierForest_actual_002723
  · exact g32p_supplierForest_actual_002770
  · exact g32p_supplierForest_actual_002811
  · exact g32p_supplierForest_actual_002886
  · exact g32p_supplierForest_actual_002961
  · exact g32p_supplierForest_actual_002962
  · exact g32p_supplierForest_actual_003062
  · exact g32p_supplierForest_actual_003131
  · exact g32p_supplierForest_actual_003181
  · exact g32p_supplierForest_actual_003246
  · exact g32p_supplierForest_actual_003251
  · exact g32p_supplierForest_actual_003280
  · exact g32p_supplierForest_actual_003282
  · exact g32p_supplierForest_actual_003316
  · exact g32p_supplierForest_actual_003321
  · exact g32p_supplierForest_actual_003408
  · exact g32p_supplierForest_actual_003461
  · exact g32p_supplierForest_actual_003492
  · exact g32p_supplierForest_actual_003510
  · exact g32p_supplierForest_actual_003532
  · exact g32p_supplierForest_actual_003536
  · exact g32p_supplierForest_actual_003541
  · exact g32p_supplierForest_actual_003606
  · exact g32p_supplierForest_actual_003672
  · exact g32p_supplierForest_actual_003694
  · exact g32p_supplierForest_actual_003744
  · exact g32p_supplierForest_actual_003799
  · exact g32p_supplierForest_actual_003800
  · exact g32p_supplierForest_actual_003980
  · exact g32p_supplierForest_actual_004180
  · exact g32p_supplierForest_actual_004212
  · exact g32p_supplierForest_actual_004242
  · exact g32p_supplierForest_actual_004256
  · exact g32p_supplierForest_actual_004321
  · exact g32p_supplierForest_actual_004482
  · exact g32p_supplierForest_actual_004546
  · exact g32p_supplierForest_actual_004693
  · exact g32p_supplierForest_actual_004696
  · exact g32p_supplierForest_actual_004701
  · exact g32p_supplierForest_actual_004729
  · exact g32p_supplierForest_actual_004808
  · exact g32p_supplierForest_actual_004814
  · exact g32p_supplierForest_actual_004817
  · exact g32p_supplierForest_actual_004936
  · exact g32p_supplierForest_actual_004966
  · exact g32p_supplierForest_actual_005025
  · exact g32p_supplierForest_actual_005060
  · exact g32p_supplierForest_actual_005070
  · exact g32p_supplierForest_actual_005092
  · exact g32p_supplierForest_actual_005094
  · exact g32p_supplierForest_actual_005100
  · exact g32p_supplierForest_actual_005138
  · exact g32p_supplierForest_actual_005146
  · exact g32p_supplierForest_actual_005235
  · exact g32p_supplierForest_actual_005256
  · exact g32p_supplierForest_actual_005280
  · exact g32p_supplierForest_actual_005284
  · exact g32p_supplierForest_actual_005327
  · exact g32p_supplierForest_actual_005331
  · exact g32p_supplierForest_actual_005345
  · exact g32p_supplierForest_actual_005352
  · exact g32p_supplierForest_actual_005355
  · exact g32p_supplierForest_actual_005375
  · exact g32p_supplierForest_actual_005465
  · exact g32p_supplierForest_actual_005475
  · exact g32p_supplierForest_actual_005480
  · exact g32p_supplierForest_actual_005543
  · exact g32p_supplierForest_actual_005549
  · exact g32p_supplierForest_actual_005565
  · exact g32p_supplierForest_actual_005706
  · exact g32p_supplierForest_actual_005707
  · exact g32p_supplierForest_actual_005837
  · exact g32p_supplierForest_actual_005846
  · exact g32p_supplierForest_actual_006020
  · exact g32p_supplierForest_actual_006039
  · exact g32p_supplierForest_actual_006063
  · exact g32p_supplierForest_actual_006094
  · exact g32p_supplierForest_actual_006097
  · exact g32p_supplierForest_actual_006141
  · exact g32p_supplierForest_actual_006171
  · exact g32p_supplierForest_actual_006175
  · exact g32p_supplierForest_actual_006185
  · exact g32p_supplierForest_actual_006210
  · exact g32p_supplierForest_actual_006223
  · exact g32p_supplierForest_actual_006269
  · exact g32p_supplierForest_actual_006367
  · exact g32p_supplierForest_actual_006391
  · exact g32p_supplierForest_actual_006423
  · exact g32p_supplierForest_actual_006438
  · exact g32p_supplierForest_actual_006503
  · exact g32p_supplierForest_actual_006537
  · exact g32p_supplierForest_actual_006538
  · exact g32p_supplierForest_actual_006558
  · exact g32p_supplierForest_actual_006574
  · exact g32p_supplierForest_actual_006590
  · exact g32p_supplierForest_actual_006593
  · exact g32p_supplierForest_actual_006641
  · exact g32p_supplierForest_actual_006667
  · exact g32p_supplierForest_actual_006754
  · exact g32p_supplierForest_actual_006764
  · exact g32p_supplierForest_actual_006788
  · exact g32p_supplierForest_actual_006822
  · exact g32p_supplierForest_actual_006837
  · exact g32p_supplierForest_actual_006847
  · exact g32p_supplierForest_actual_006884
  · exact g32p_supplierForest_actual_006925
  · exact g32p_supplierForest_actual_007040
  · exact g32p_supplierForest_actual_007148
  · exact g32p_supplierForest_actual_007249
  · exact g32p_supplierForest_actual_007262
  · exact g32p_supplierForest_actual_007289
  · exact g32p_supplierForest_actual_007302
  · exact g32p_supplierForest_actual_007336
  · exact g32p_supplierForest_actual_007350
  · exact g32p_supplierForest_actual_007431
  · exact g32p_supplierForest_actual_007440
  · exact g32p_supplierForest_actual_007538
  · exact g32p_supplierForest_actual_007623
  · exact g32p_supplierForest_actual_007634
  · exact g32p_supplierForest_actual_007644
  · exact g32p_supplierForest_actual_007668
  · exact g32p_supplierForest_actual_007691
  · exact g32p_supplierForest_actual_007709
  · exact g32p_supplierForest_actual_007726
  · exact g32p_supplierForest_actual_007803
  · exact g32p_supplierForest_actual_007822
  · exact g32p_supplierForest_actual_007828
  · exact g32p_supplierForest_actual_007832
  · exact g32p_supplierForest_actual_007837
  · exact g32p_supplierForest_actual_007845
  · exact g32p_supplierForest_actual_007884
  · exact g32p_supplierForest_actual_007885
  · exact g32p_supplierForest_actual_007974
  · exact g32p_supplierForest_actual_007976
  · exact g32p_supplierForest_actual_007994
  · exact g32p_supplierForest_actual_007996
  · exact g32p_supplierForest_actual_008034
  · exact g32p_supplierForest_actual_008096
  · exact g32p_supplierForest_actual_008127
  · exact g32p_supplierForest_actual_008166
  · exact g32p_supplierForest_actual_008198
  · exact g32p_supplierForest_actual_008252
  · exact g32p_supplierForest_actual_008262
  · exact g32p_supplierForest_actual_008294
  · exact g32p_supplierForest_actual_008307
  · exact g32p_supplierForest_actual_008424
  · exact g32p_supplierForest_actual_008440
  · exact g32p_supplierForest_actual_008466
  · exact g32p_supplierForest_actual_008482
  · exact g32p_supplierForest_actual_008534
  · exact g32p_supplierForest_actual_008548
  · exact g32p_supplierForest_actual_008578
  · exact g32p_supplierForest_actual_008583
  · exact g32p_supplierForest_actual_008621
  · exact g32p_supplierForest_actual_008628
  · exact g32p_supplierForest_actual_008645
  · exact g32p_supplierForest_actual_008681
  · exact g32p_supplierForest_actual_008775
  · exact g32p_supplierForest_actual_008779
  · exact g32p_supplierForest_actual_008805
  · exact g32p_supplierForest_actual_008814
  · exact g32p_supplierForest_actual_008816
  · exact g32p_supplierForest_actual_008873
  · exact g32p_supplierForest_actual_008890
  · exact g32p_supplierForest_actual_008894
  · exact g32p_supplierForest_actual_008898
  · exact g32p_supplierForest_actual_008940
  · exact g32p_supplierForest_actual_008942
  · exact g32p_supplierForest_actual_008971
  · exact g32p_supplierForest_actual_008996
  · exact g32p_supplierForest_actual_009041
  · exact g32p_supplierForest_actual_009092
  · exact g32p_supplierForest_actual_009205
  · exact g32p_supplierForest_actual_009213
  · exact g32p_supplierForest_actual_009226
  · exact g32p_supplierForest_actual_009419
  · exact g32p_supplierForest_actual_009432
  · exact g32p_supplierForest_actual_009444
  · exact g32p_supplierForest_actual_009471
  · exact g32p_supplierForest_actual_009520
  · exact g32p_supplierForest_actual_009523
  · exact g32p_supplierForest_actual_009583
  · exact g32p_supplierForest_actual_009586
  · exact g32p_supplierForest_actual_009611
  · exact g32p_supplierForest_actual_009618
  · exact g32p_supplierForest_actual_009667
  · exact g32p_supplierForest_actual_009718
  · exact g32p_supplierForest_actual_009728
  · exact g32p_supplierForest_actual_009734
  · exact g32p_supplierForest_actual_009742
  · exact g32p_supplierForest_actual_009758
  · exact g32p_supplierForest_actual_009761
  · exact g32p_supplierForest_actual_009801
  · exact g32p_supplierForest_actual_009812
  · exact g32p_supplierForest_actual_009817
  · exact g32p_supplierForest_actual_009818
  · exact g32p_supplierForest_actual_009841
  · exact g32p_supplierForest_actual_009953
  · exact g32p_supplierForest_actual_010059
  · exact g32p_supplierForest_actual_010113
  · exact g32p_supplierForest_actual_010134
  · exact g32p_supplierForest_actual_010147
  · exact g32p_supplierForest_actual_010206
  · exact g32p_supplierForest_actual_010272
  · exact g32p_supplierForest_actual_010299
  · exact g32p_supplierForest_actual_010350
  · exact g32p_supplierForest_actual_010399
  · exact g32p_supplierForest_actual_010414
  · exact g32p_supplierForest_actual_010486
  · exact g32p_supplierForest_actual_010555
  · exact g32p_supplierForest_actual_010608
  · exact g32p_supplierForest_actual_010619
  · exact g32p_supplierForest_actual_010641
  · exact g32p_supplierForest_actual_010708
  · exact g32p_supplierForest_actual_010713
  · exact g32p_supplierForest_actual_010740
  · exact g32p_supplierForest_actual_010743
  · exact g32p_supplierForest_actual_010794
  · exact g32p_supplierForest_actual_010808
  · exact g32p_supplierForest_actual_010831
  · exact g32p_supplierForest_actual_010888

def g32p_supplierForest_nodes_113 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_010951 else g32p_supplierForest_node_011035) else (if i.val < 3 then g32p_supplierForest_node_011052 else g32p_supplierForest_node_011084)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_011180 else g32p_supplierForest_node_011203) else (if i.val < 7 then g32p_supplierForest_node_011250 else g32p_supplierForest_node_011278))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_011285 else g32p_supplierForest_node_011287) else (if i.val < 11 then g32p_supplierForest_node_011299 else g32p_supplierForest_node_011317)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_011323 else g32p_supplierForest_node_011324) else (if i.val < 15 then g32p_supplierForest_node_011403 else g32p_supplierForest_node_011404)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_011426 else g32p_supplierForest_node_011445) else (if i.val < 19 then g32p_supplierForest_node_011450 else g32p_supplierForest_node_011460)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_011528 else g32p_supplierForest_node_011649) else (if i.val < 23 then g32p_supplierForest_node_011712 else g32p_supplierForest_node_011724))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_011816 else g32p_supplierForest_node_011819) else (if i.val < 27 then g32p_supplierForest_node_011836 else g32p_supplierForest_node_011910)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_011915 else g32p_supplierForest_node_011928) else (if i.val < 31 then g32p_supplierForest_node_011987 else g32p_supplierForest_node_012002))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_012019 else g32p_supplierForest_node_012084) else (if i.val < 35 then g32p_supplierForest_node_012100 else g32p_supplierForest_node_012101)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_012130 else g32p_supplierForest_node_012132) else (if i.val < 39 then g32p_supplierForest_node_012158 else g32p_supplierForest_node_012247))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_012260 else g32p_supplierForest_node_012429) else (if i.val < 43 then g32p_supplierForest_node_012508 else g32p_supplierForest_node_012566)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_012580 else g32p_supplierForest_node_012600) else (if i.val < 47 then g32p_supplierForest_node_012716 else g32p_supplierForest_node_012720)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_012758 else g32p_supplierForest_node_012776) else (if i.val < 51 then g32p_supplierForest_node_012806 else g32p_supplierForest_node_012811)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_012874 else g32p_supplierForest_node_012891) else (if i.val < 55 then g32p_supplierForest_node_012897 else g32p_supplierForest_node_012943))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_012956 else g32p_supplierForest_node_013018) else (if i.val < 59 then g32p_supplierForest_node_013029 else g32p_supplierForest_node_013032)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_013037 else g32p_supplierForest_node_013041) else (if i.val < 63 then g32p_supplierForest_node_013082 else g32p_supplierForest_node_013089)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_013104 else g32p_supplierForest_node_013117) else (if i.val < 67 then g32p_supplierForest_node_013118 else g32p_supplierForest_node_013205)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_013209 else g32p_supplierForest_node_013334) else (if i.val < 71 then g32p_supplierForest_node_013409 else g32p_supplierForest_node_013414))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_013424 else g32p_supplierForest_node_013431) else (if i.val < 75 then g32p_supplierForest_node_013526 else g32p_supplierForest_node_013557)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_013590 else g32p_supplierForest_node_013595) else (if i.val < 79 then g32p_supplierForest_node_013596 else g32p_supplierForest_node_013607)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_013645 else g32p_supplierForest_node_013655) else (if i.val < 83 then g32p_supplierForest_node_013805 else g32p_supplierForest_node_013836)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_013866 else g32p_supplierForest_node_013977) else (if i.val < 87 then g32p_supplierForest_node_013999 else g32p_supplierForest_node_014026))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_014068 else g32p_supplierForest_node_014088) else (if i.val < 91 then g32p_supplierForest_node_014140 else g32p_supplierForest_node_014294)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_014302 else g32p_supplierForest_node_014331) else (if i.val < 95 then g32p_supplierForest_node_014388 else g32p_supplierForest_node_014405))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_014418 else g32p_supplierForest_node_014443) else (if i.val < 99 then g32p_supplierForest_node_014473 else g32p_supplierForest_node_014478)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_014493 else g32p_supplierForest_node_014524) else (if i.val < 103 then g32p_supplierForest_node_014539 else g32p_supplierForest_node_014585))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_014627 else g32p_supplierForest_node_014642) else (if i.val < 107 then g32p_supplierForest_node_014756 else g32p_supplierForest_node_014763)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_014771 else g32p_supplierForest_node_014804) else (if i.val < 111 then g32p_supplierForest_node_014896 else g32p_supplierForest_node_014906)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_014907 else g32p_supplierForest_node_014923) else (if i.val < 115 then g32p_supplierForest_node_014944 else g32p_supplierForest_node_015063)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_015081 else g32p_supplierForest_node_015085) else (if i.val < 119 then g32p_supplierForest_node_015106 else g32p_supplierForest_node_015115))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_015132 else g32p_supplierForest_node_015142) else (if i.val < 123 then g32p_supplierForest_node_015164 else g32p_supplierForest_node_015197)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_015377 else g32p_supplierForest_node_015381) else (if i.val < 127 then g32p_supplierForest_node_015410 else g32p_supplierForest_node_015447))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_015460 else g32p_supplierForest_node_015489) else (if i.val < 131 then g32p_supplierForest_node_015492 else g32p_supplierForest_node_015497)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_015503 else g32p_supplierForest_node_015531) else (if i.val < 135 then g32p_supplierForest_node_015548 else g32p_supplierForest_node_015578))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_015654 else g32p_supplierForest_node_015671) else (if i.val < 139 then g32p_supplierForest_node_015712 else g32p_supplierForest_node_015728)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_015773 else g32p_supplierForest_node_015792) else (if i.val < 143 then g32p_supplierForest_node_015808 else g32p_supplierForest_node_015814)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_016118 else g32p_supplierForest_node_016150) else (if i.val < 147 then g32p_supplierForest_node_016177 else g32p_supplierForest_node_016205)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_016258 else g32p_supplierForest_node_016286) else (if i.val < 151 then g32p_supplierForest_node_016294 else g32p_supplierForest_node_016403))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_016458 else g32p_supplierForest_node_016472) else (if i.val < 155 then g32p_supplierForest_node_016494 else g32p_supplierForest_node_016503)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_016521 else g32p_supplierForest_node_016549) else (if i.val < 159 then g32p_supplierForest_node_016557 else g32p_supplierForest_node_016559))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_016610 else g32p_supplierForest_node_016611) else (if i.val < 163 then g32p_supplierForest_node_016640 else g32p_supplierForest_node_016681)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_016687 else g32p_supplierForest_node_016714) else (if i.val < 167 then g32p_supplierForest_node_016718 else g32p_supplierForest_node_016729))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_016734 else g32p_supplierForest_node_016793) else (if i.val < 171 then g32p_supplierForest_node_016815 else g32p_supplierForest_node_016867)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_016899 else g32p_supplierForest_node_017036) else (if i.val < 175 then g32p_supplierForest_node_017074 else g32p_supplierForest_node_017113)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_017115 else g32p_supplierForest_node_017125) else (if i.val < 179 then g32p_supplierForest_node_017137 else g32p_supplierForest_node_017178)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_017208 else g32p_supplierForest_node_017248) else (if i.val < 183 then g32p_supplierForest_node_017297 else g32p_supplierForest_node_017306))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_017327 else g32p_supplierForest_node_017329) else (if i.val < 187 then g32p_supplierForest_node_017398 else g32p_supplierForest_node_017412)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_017517 else g32p_supplierForest_node_017553) else (if i.val < 191 then g32p_supplierForest_node_017560 else g32p_supplierForest_node_017633)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_017642 else g32p_supplierForest_node_017738) else (if i.val < 195 then g32p_supplierForest_node_017772 else g32p_supplierForest_node_017823)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_017831 else g32p_supplierForest_node_017838) else (if i.val < 199 then g32p_supplierForest_node_017862 else g32p_supplierForest_node_017867))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_017918 else g32p_supplierForest_node_017938) else (if i.val < 203 then g32p_supplierForest_node_017961 else g32p_supplierForest_node_018011)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_018050 else g32p_supplierForest_node_018107) else (if i.val < 207 then g32p_supplierForest_node_018120 else g32p_supplierForest_node_018159)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_018179 else g32p_supplierForest_node_018185) else (if i.val < 211 then g32p_supplierForest_node_018189 else g32p_supplierForest_node_018229)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_018244 else g32p_supplierForest_node_018284) else (if i.val < 215 then g32p_supplierForest_node_018379 else g32p_supplierForest_node_018412))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_018508 else g32p_supplierForest_node_018522) else (if i.val < 219 then g32p_supplierForest_node_018538 else g32p_supplierForest_node_018546)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_018648 else g32p_supplierForest_node_018685) else (if i.val < 223 then g32p_supplierForest_node_018719 else g32p_supplierForest_node_018758))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_018787 else g32p_supplierForest_node_018796) else (if i.val < 227 then g32p_supplierForest_node_018826 else g32p_supplierForest_node_018911)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_018923 else g32p_supplierForest_node_018934) else (if i.val < 231 then g32p_supplierForest_node_018947 else g32p_supplierForest_node_019062))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_019095 else g32p_supplierForest_node_019113) else (if i.val < 235 then g32p_supplierForest_node_019181 else g32p_supplierForest_node_019209)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_019253 else g32p_supplierForest_node_019277) else (if i.val < 239 then g32p_supplierForest_node_019308 else g32p_supplierForest_node_019380)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_019400 else g32p_supplierForest_node_019416) else (if i.val < 243 then g32p_supplierForest_node_019434 else g32p_supplierForest_node_019461)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_019475 else g32p_supplierForest_node_019479) else (if i.val < 247 then g32p_supplierForest_node_019513 else g32p_supplierForest_node_019520))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_019532 else g32p_supplierForest_node_019534) else (if i.val < 251 then g32p_supplierForest_node_019547 else g32p_supplierForest_node_019552)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_019588 else g32p_supplierForest_node_019598) else (if i.val < 255 then g32p_supplierForest_node_019599 else g32p_supplierForest_node_019660))))))))

def g32p_supplierForest_classes_113 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 21 else 21) else (if i.val < 3 then 22 else 20)) else (if i.val < 6 then (if i.val < 5 then 38 else 21) else (if i.val < 7 then 38 else 40))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 40) else (if i.val < 11 then 38 else 20)) else (if i.val < 14 then (if i.val < 13 then 22 else 22) else (if i.val < 15 then 38 else 40)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 40) else (if i.val < 19 then 7 else 38)) else (if i.val < 22 then (if i.val < 21 then 38 else 20) else (if i.val < 23 then 22 else 21))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 39 else 40) else (if i.val < 27 then 22 else 38)) else (if i.val < 30 then (if i.val < 29 then 38 else 7) else (if i.val < 31 then 38 else 22))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 22 else 39) else (if i.val < 35 then 22 else 38)) else (if i.val < 38 then (if i.val < 37 then 21 else 43) else (if i.val < 39 then 21 else 20))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 39 else 47) else (if i.val < 43 then 12 else 49)) else (if i.val < 46 then (if i.val < 45 then 49 else 46) else (if i.val < 47 then 50 else 9)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 25 else 50) else (if i.val < 51 then 10 else 46)) else (if i.val < 54 then (if i.val < 53 then 49 else 49) else (if i.val < 55 then 25 else 47))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 9 else 26) else (if i.val < 59 then 12 else 49)) else (if i.val < 62 then (if i.val < 61 then 9 else 11) else (if i.val < 63 then 10 else 10)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 47) else (if i.val < 67 then 47 else 50)) else (if i.val < 70 then (if i.val < 69 then 49 else 26) else (if i.val < 71 then 49 else 48))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 50 else 49) else (if i.val < 75 then 12 else 25)) else (if i.val < 78 then (if i.val < 77 then 10 else 46) else (if i.val < 79 then 27 else 11)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 46 else 45) else (if i.val < 83 then 10 else 25)) else (if i.val < 86 then (if i.val < 85 then 10 else 49) else (if i.val < 87 then 9 else 10))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 50 else 25) else (if i.val < 91 then 49 else 48)) else (if i.val < 94 then (if i.val < 93 then 12 else 10) else (if i.val < 95 then 25 else 52))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 12 else 27) else (if i.val < 99 then 27 else 50)) else (if i.val < 102 then (if i.val < 101 then 27 else 10) else (if i.val < 103 then 48 else 12))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 9 else 47) else (if i.val < 107 then 48 else 47)) else (if i.val < 110 then (if i.val < 109 then 50 else 49) else (if i.val < 111 then 25 else 48)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 47 else 48) else (if i.val < 115 then 49 else 47)) else (if i.val < 118 then (if i.val < 117 then 49 else 49) else (if i.val < 119 then 47 else 25))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 10 else 27) else (if i.val < 123 then 47 else 10)) else (if i.val < 126 then (if i.val < 125 then 47 else 9) else (if i.val < 127 then 10 else 47))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 48) else (if i.val < 131 then 52 else 47)) else (if i.val < 134 then (if i.val < 133 then 25 else 10) else (if i.val < 135 then 49 else 10))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 49 else 49) else (if i.val < 139 then 25 else 49)) else (if i.val < 142 then (if i.val < 141 then 25 else 9) else (if i.val < 143 then 47 else 50)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 48 else 50) else (if i.val < 147 then 47 else 25)) else (if i.val < 150 then (if i.val < 149 then 10 else 25) else (if i.val < 151 then 46 else 48))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 49 else 49) else (if i.val < 155 then 50 else 48)) else (if i.val < 158 then (if i.val < 157 then 49 else 11) else (if i.val < 159 then 56 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 48 else 50) else (if i.val < 163 then 10 else 49)) else (if i.val < 166 then (if i.val < 165 then 10 else 49) else (if i.val < 167 then 25 else 12))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 25 else 26) else (if i.val < 171 then 47 else 25)) else (if i.val < 174 then (if i.val < 173 then 10 else 10) else (if i.val < 175 then 49 else 12)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 47 else 50) else (if i.val < 179 then 10 else 47)) else (if i.val < 182 then (if i.val < 181 then 46 else 49) else (if i.val < 183 then 26 else 26))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 12 else 27) else (if i.val < 187 then 47 else 48)) else (if i.val < 190 then (if i.val < 189 then 47 else 9) else (if i.val < 191 then 49 else 25)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 10 else 47) else (if i.val < 195 then 49 else 26)) else (if i.val < 198 then (if i.val < 197 then 26 else 49) else (if i.val < 199 then 26 else 26))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 47 else 49) else (if i.val < 203 then 46 else 49)) else (if i.val < 206 then (if i.val < 205 then 50 else 49) else (if i.val < 207 then 48 else 27)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 49 else 49) else (if i.val < 211 then 50 else 26)) else (if i.val < 214 then (if i.val < 213 then 26 else 49) else (if i.val < 215 then 50 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 10 else 49) else (if i.val < 219 then 12 else 56)) else (if i.val < 222 then (if i.val < 221 then 9 else 9) else (if i.val < 223 then 12 else 47))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 46 else 49) else (if i.val < 227 then 49 else 10)) else (if i.val < 230 then (if i.val < 229 then 12 else 49) else (if i.val < 231 then 47 else 10))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 46 else 12) else (if i.val < 235 then 26 else 45)) else (if i.val < 238 then (if i.val < 237 then 46 else 49) else (if i.val < 239 then 26 else 50)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 9 else 9) else (if i.val < 243 then 10 else 49)) else (if i.val < 246 then (if i.val < 245 then 25 else 10) else (if i.val < 247 then 26 else 9))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 27 else 12) else (if i.val < 251 then 25 else 49)) else (if i.val < 254 then (if i.val < 253 then 46 else 27) else (if i.val < 255 then 25 else 27))))))))

theorem g32p_supplierForest_actual_113 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_113 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_113 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_010951
  · exact g32p_supplierForest_actual_011035
  · exact g32p_supplierForest_actual_011052
  · exact g32p_supplierForest_actual_011084
  · exact g32p_supplierForest_actual_011180
  · exact g32p_supplierForest_actual_011203
  · exact g32p_supplierForest_actual_011250
  · exact g32p_supplierForest_actual_011278
  · exact g32p_supplierForest_actual_011285
  · exact g32p_supplierForest_actual_011287
  · exact g32p_supplierForest_actual_011299
  · exact g32p_supplierForest_actual_011317
  · exact g32p_supplierForest_actual_011323
  · exact g32p_supplierForest_actual_011324
  · exact g32p_supplierForest_actual_011403
  · exact g32p_supplierForest_actual_011404
  · exact g32p_supplierForest_actual_011426
  · exact g32p_supplierForest_actual_011445
  · exact g32p_supplierForest_actual_011450
  · exact g32p_supplierForest_actual_011460
  · exact g32p_supplierForest_actual_011528
  · exact g32p_supplierForest_actual_011649
  · exact g32p_supplierForest_actual_011712
  · exact g32p_supplierForest_actual_011724
  · exact g32p_supplierForest_actual_011816
  · exact g32p_supplierForest_actual_011819
  · exact g32p_supplierForest_actual_011836
  · exact g32p_supplierForest_actual_011910
  · exact g32p_supplierForest_actual_011915
  · exact g32p_supplierForest_actual_011928
  · exact g32p_supplierForest_actual_011987
  · exact g32p_supplierForest_actual_012002
  · exact g32p_supplierForest_actual_012019
  · exact g32p_supplierForest_actual_012084
  · exact g32p_supplierForest_actual_012100
  · exact g32p_supplierForest_actual_012101
  · exact g32p_supplierForest_actual_012130
  · exact g32p_supplierForest_actual_012132
  · exact g32p_supplierForest_actual_012158
  · exact g32p_supplierForest_actual_012247
  · exact g32p_supplierForest_actual_012260
  · exact g32p_supplierForest_actual_012429
  · exact g32p_supplierForest_actual_012508
  · exact g32p_supplierForest_actual_012566
  · exact g32p_supplierForest_actual_012580
  · exact g32p_supplierForest_actual_012600
  · exact g32p_supplierForest_actual_012716
  · exact g32p_supplierForest_actual_012720
  · exact g32p_supplierForest_actual_012758
  · exact g32p_supplierForest_actual_012776
  · exact g32p_supplierForest_actual_012806
  · exact g32p_supplierForest_actual_012811
  · exact g32p_supplierForest_actual_012874
  · exact g32p_supplierForest_actual_012891
  · exact g32p_supplierForest_actual_012897
  · exact g32p_supplierForest_actual_012943
  · exact g32p_supplierForest_actual_012956
  · exact g32p_supplierForest_actual_013018
  · exact g32p_supplierForest_actual_013029
  · exact g32p_supplierForest_actual_013032
  · exact g32p_supplierForest_actual_013037
  · exact g32p_supplierForest_actual_013041
  · exact g32p_supplierForest_actual_013082
  · exact g32p_supplierForest_actual_013089
  · exact g32p_supplierForest_actual_013104
  · exact g32p_supplierForest_actual_013117
  · exact g32p_supplierForest_actual_013118
  · exact g32p_supplierForest_actual_013205
  · exact g32p_supplierForest_actual_013209
  · exact g32p_supplierForest_actual_013334
  · exact g32p_supplierForest_actual_013409
  · exact g32p_supplierForest_actual_013414
  · exact g32p_supplierForest_actual_013424
  · exact g32p_supplierForest_actual_013431
  · exact g32p_supplierForest_actual_013526
  · exact g32p_supplierForest_actual_013557
  · exact g32p_supplierForest_actual_013590
  · exact g32p_supplierForest_actual_013595
  · exact g32p_supplierForest_actual_013596
  · exact g32p_supplierForest_actual_013607
  · exact g32p_supplierForest_actual_013645
  · exact g32p_supplierForest_actual_013655
  · exact g32p_supplierForest_actual_013805
  · exact g32p_supplierForest_actual_013836
  · exact g32p_supplierForest_actual_013866
  · exact g32p_supplierForest_actual_013977
  · exact g32p_supplierForest_actual_013999
  · exact g32p_supplierForest_actual_014026
  · exact g32p_supplierForest_actual_014068
  · exact g32p_supplierForest_actual_014088
  · exact g32p_supplierForest_actual_014140
  · exact g32p_supplierForest_actual_014294
  · exact g32p_supplierForest_actual_014302
  · exact g32p_supplierForest_actual_014331
  · exact g32p_supplierForest_actual_014388
  · exact g32p_supplierForest_actual_014405
  · exact g32p_supplierForest_actual_014418
  · exact g32p_supplierForest_actual_014443
  · exact g32p_supplierForest_actual_014473
  · exact g32p_supplierForest_actual_014478
  · exact g32p_supplierForest_actual_014493
  · exact g32p_supplierForest_actual_014524
  · exact g32p_supplierForest_actual_014539
  · exact g32p_supplierForest_actual_014585
  · exact g32p_supplierForest_actual_014627
  · exact g32p_supplierForest_actual_014642
  · exact g32p_supplierForest_actual_014756
  · exact g32p_supplierForest_actual_014763
  · exact g32p_supplierForest_actual_014771
  · exact g32p_supplierForest_actual_014804
  · exact g32p_supplierForest_actual_014896
  · exact g32p_supplierForest_actual_014906
  · exact g32p_supplierForest_actual_014907
  · exact g32p_supplierForest_actual_014923
  · exact g32p_supplierForest_actual_014944
  · exact g32p_supplierForest_actual_015063
  · exact g32p_supplierForest_actual_015081
  · exact g32p_supplierForest_actual_015085
  · exact g32p_supplierForest_actual_015106
  · exact g32p_supplierForest_actual_015115
  · exact g32p_supplierForest_actual_015132
  · exact g32p_supplierForest_actual_015142
  · exact g32p_supplierForest_actual_015164
  · exact g32p_supplierForest_actual_015197
  · exact g32p_supplierForest_actual_015377
  · exact g32p_supplierForest_actual_015381
  · exact g32p_supplierForest_actual_015410
  · exact g32p_supplierForest_actual_015447
  · exact g32p_supplierForest_actual_015460
  · exact g32p_supplierForest_actual_015489
  · exact g32p_supplierForest_actual_015492
  · exact g32p_supplierForest_actual_015497
  · exact g32p_supplierForest_actual_015503
  · exact g32p_supplierForest_actual_015531
  · exact g32p_supplierForest_actual_015548
  · exact g32p_supplierForest_actual_015578
  · exact g32p_supplierForest_actual_015654
  · exact g32p_supplierForest_actual_015671
  · exact g32p_supplierForest_actual_015712
  · exact g32p_supplierForest_actual_015728
  · exact g32p_supplierForest_actual_015773
  · exact g32p_supplierForest_actual_015792
  · exact g32p_supplierForest_actual_015808
  · exact g32p_supplierForest_actual_015814
  · exact g32p_supplierForest_actual_016118
  · exact g32p_supplierForest_actual_016150
  · exact g32p_supplierForest_actual_016177
  · exact g32p_supplierForest_actual_016205
  · exact g32p_supplierForest_actual_016258
  · exact g32p_supplierForest_actual_016286
  · exact g32p_supplierForest_actual_016294
  · exact g32p_supplierForest_actual_016403
  · exact g32p_supplierForest_actual_016458
  · exact g32p_supplierForest_actual_016472
  · exact g32p_supplierForest_actual_016494
  · exact g32p_supplierForest_actual_016503
  · exact g32p_supplierForest_actual_016521
  · exact g32p_supplierForest_actual_016549
  · exact g32p_supplierForest_actual_016557
  · exact g32p_supplierForest_actual_016559
  · exact g32p_supplierForest_actual_016610
  · exact g32p_supplierForest_actual_016611
  · exact g32p_supplierForest_actual_016640
  · exact g32p_supplierForest_actual_016681
  · exact g32p_supplierForest_actual_016687
  · exact g32p_supplierForest_actual_016714
  · exact g32p_supplierForest_actual_016718
  · exact g32p_supplierForest_actual_016729
  · exact g32p_supplierForest_actual_016734
  · exact g32p_supplierForest_actual_016793
  · exact g32p_supplierForest_actual_016815
  · exact g32p_supplierForest_actual_016867
  · exact g32p_supplierForest_actual_016899
  · exact g32p_supplierForest_actual_017036
  · exact g32p_supplierForest_actual_017074
  · exact g32p_supplierForest_actual_017113
  · exact g32p_supplierForest_actual_017115
  · exact g32p_supplierForest_actual_017125
  · exact g32p_supplierForest_actual_017137
  · exact g32p_supplierForest_actual_017178
  · exact g32p_supplierForest_actual_017208
  · exact g32p_supplierForest_actual_017248
  · exact g32p_supplierForest_actual_017297
  · exact g32p_supplierForest_actual_017306
  · exact g32p_supplierForest_actual_017327
  · exact g32p_supplierForest_actual_017329
  · exact g32p_supplierForest_actual_017398
  · exact g32p_supplierForest_actual_017412
  · exact g32p_supplierForest_actual_017517
  · exact g32p_supplierForest_actual_017553
  · exact g32p_supplierForest_actual_017560
  · exact g32p_supplierForest_actual_017633
  · exact g32p_supplierForest_actual_017642
  · exact g32p_supplierForest_actual_017738
  · exact g32p_supplierForest_actual_017772
  · exact g32p_supplierForest_actual_017823
  · exact g32p_supplierForest_actual_017831
  · exact g32p_supplierForest_actual_017838
  · exact g32p_supplierForest_actual_017862
  · exact g32p_supplierForest_actual_017867
  · exact g32p_supplierForest_actual_017918
  · exact g32p_supplierForest_actual_017938
  · exact g32p_supplierForest_actual_017961
  · exact g32p_supplierForest_actual_018011
  · exact g32p_supplierForest_actual_018050
  · exact g32p_supplierForest_actual_018107
  · exact g32p_supplierForest_actual_018120
  · exact g32p_supplierForest_actual_018159
  · exact g32p_supplierForest_actual_018179
  · exact g32p_supplierForest_actual_018185
  · exact g32p_supplierForest_actual_018189
  · exact g32p_supplierForest_actual_018229
  · exact g32p_supplierForest_actual_018244
  · exact g32p_supplierForest_actual_018284
  · exact g32p_supplierForest_actual_018379
  · exact g32p_supplierForest_actual_018412
  · exact g32p_supplierForest_actual_018508
  · exact g32p_supplierForest_actual_018522
  · exact g32p_supplierForest_actual_018538
  · exact g32p_supplierForest_actual_018546
  · exact g32p_supplierForest_actual_018648
  · exact g32p_supplierForest_actual_018685
  · exact g32p_supplierForest_actual_018719
  · exact g32p_supplierForest_actual_018758
  · exact g32p_supplierForest_actual_018787
  · exact g32p_supplierForest_actual_018796
  · exact g32p_supplierForest_actual_018826
  · exact g32p_supplierForest_actual_018911
  · exact g32p_supplierForest_actual_018923
  · exact g32p_supplierForest_actual_018934
  · exact g32p_supplierForest_actual_018947
  · exact g32p_supplierForest_actual_019062
  · exact g32p_supplierForest_actual_019095
  · exact g32p_supplierForest_actual_019113
  · exact g32p_supplierForest_actual_019181
  · exact g32p_supplierForest_actual_019209
  · exact g32p_supplierForest_actual_019253
  · exact g32p_supplierForest_actual_019277
  · exact g32p_supplierForest_actual_019308
  · exact g32p_supplierForest_actual_019380
  · exact g32p_supplierForest_actual_019400
  · exact g32p_supplierForest_actual_019416
  · exact g32p_supplierForest_actual_019434
  · exact g32p_supplierForest_actual_019461
  · exact g32p_supplierForest_actual_019475
  · exact g32p_supplierForest_actual_019479
  · exact g32p_supplierForest_actual_019513
  · exact g32p_supplierForest_actual_019520
  · exact g32p_supplierForest_actual_019532
  · exact g32p_supplierForest_actual_019534
  · exact g32p_supplierForest_actual_019547
  · exact g32p_supplierForest_actual_019552
  · exact g32p_supplierForest_actual_019588
  · exact g32p_supplierForest_actual_019598
  · exact g32p_supplierForest_actual_019599
  · exact g32p_supplierForest_actual_019660

def g32p_supplierForest_nodes_114 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_019666 else g32p_supplierForest_node_019682) else (if i.val < 3 then g32p_supplierForest_node_019689 else g32p_supplierForest_node_019691)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_019699 else g32p_supplierForest_node_019744) else (if i.val < 7 then g32p_supplierForest_node_019746 else g32p_supplierForest_node_019762))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_019873 else g32p_supplierForest_node_019923) else (if i.val < 11 then g32p_supplierForest_node_019933 else g32p_supplierForest_node_019934)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_019966 else g32p_supplierForest_node_019992) else (if i.val < 15 then g32p_supplierForest_node_019996 else g32p_supplierForest_node_020083)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_020106 else g32p_supplierForest_node_020111) else (if i.val < 19 then g32p_supplierForest_node_020116 else g32p_supplierForest_node_020163)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_020193 else g32p_supplierForest_node_020222) else (if i.val < 23 then g32p_supplierForest_node_020226 else g32p_supplierForest_node_020289))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_020296 else g32p_supplierForest_node_020353) else (if i.val < 27 then g32p_supplierForest_node_020389 else g32p_supplierForest_node_020407)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_020485 else g32p_supplierForest_node_020500) else (if i.val < 31 then g32p_supplierForest_node_020526 else g32p_supplierForest_node_020552))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_020670 else g32p_supplierForest_node_020726) else (if i.val < 35 then g32p_supplierForest_node_020767 else g32p_supplierForest_node_020770)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_020819 else g32p_supplierForest_node_020832) else (if i.val < 39 then g32p_supplierForest_node_020869 else g32p_supplierForest_node_020897))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_020902 else g32p_supplierForest_node_020945) else (if i.val < 43 then g32p_supplierForest_node_020984 else g32p_supplierForest_node_020988)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_021066 else g32p_supplierForest_node_021083) else (if i.val < 47 then g32p_supplierForest_node_021087 else g32p_supplierForest_node_021114)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_021153 else g32p_supplierForest_node_021185) else (if i.val < 51 then g32p_supplierForest_node_021186 else g32p_supplierForest_node_021240)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_021288 else g32p_supplierForest_node_021307) else (if i.val < 55 then g32p_supplierForest_node_021327 else g32p_supplierForest_node_021349))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_021353 else g32p_supplierForest_node_021356) else (if i.val < 59 then g32p_supplierForest_node_021376 else g32p_supplierForest_node_021396)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_021442 else g32p_supplierForest_node_021471) else (if i.val < 63 then g32p_supplierForest_node_021523 else g32p_supplierForest_node_021551)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_021606 else g32p_supplierForest_node_021653) else (if i.val < 67 then g32p_supplierForest_node_021795 else g32p_supplierForest_node_021828)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_021958 else g32p_supplierForest_node_022011) else (if i.val < 71 then g32p_supplierForest_node_022012 else g32p_supplierForest_node_022035))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_022109 else g32p_supplierForest_node_022146) else (if i.val < 75 then g32p_supplierForest_node_022174 else g32p_supplierForest_node_022178)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_022204 else g32p_supplierForest_node_022247) else (if i.val < 79 then g32p_supplierForest_node_022272 else g32p_supplierForest_node_022345)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_022354 else g32p_supplierForest_node_022366) else (if i.val < 83 then g32p_supplierForest_node_022372 else g32p_supplierForest_node_022403)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_022428 else g32p_supplierForest_node_022430) else (if i.val < 87 then g32p_supplierForest_node_022467 else g32p_supplierForest_node_022492))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_022496 else g32p_supplierForest_node_022509) else (if i.val < 91 then g32p_supplierForest_node_022525 else g32p_supplierForest_node_022564)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_022594 else g32p_supplierForest_node_022614) else (if i.val < 95 then g32p_supplierForest_node_022673 else g32p_supplierForest_node_022676))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_022682 else g32p_supplierForest_node_022698) else (if i.val < 99 then g32p_supplierForest_node_022737 else g32p_supplierForest_node_022807)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_022812 else g32p_supplierForest_node_022846) else (if i.val < 103 then g32p_supplierForest_node_022877 else g32p_supplierForest_node_022889))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_022900 else g32p_supplierForest_node_022904) else (if i.val < 107 then g32p_supplierForest_node_022944 else g32p_supplierForest_node_022949)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_022989 else g32p_supplierForest_node_022999) else (if i.val < 111 then g32p_supplierForest_node_023018 else g32p_supplierForest_node_023033)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_023036 else g32p_supplierForest_node_023104) else (if i.val < 115 then g32p_supplierForest_node_023186 else g32p_supplierForest_node_023201)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_023234 else g32p_supplierForest_node_023322) else (if i.val < 119 then g32p_supplierForest_node_023370 else g32p_supplierForest_node_023435))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_023499 else g32p_supplierForest_node_023528) else (if i.val < 123 then g32p_supplierForest_node_023532 else g32p_supplierForest_node_023588)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_023589 else g32p_supplierForest_node_023615) else (if i.val < 127 then g32p_supplierForest_node_023624 else g32p_supplierForest_node_023631))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_023655 else g32p_supplierForest_node_023678) else (if i.val < 131 then g32p_supplierForest_node_023709 else g32p_supplierForest_node_023714)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_023728 else g32p_supplierForest_node_023797) else (if i.val < 135 then g32p_supplierForest_node_023798 else g32p_supplierForest_node_023964))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_023990 else g32p_supplierForest_node_024000) else (if i.val < 139 then g32p_supplierForest_node_024001 else g32p_supplierForest_node_024007)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_024025 else g32p_supplierForest_node_024123) else (if i.val < 143 then g32p_supplierForest_node_024154 else g32p_supplierForest_node_024168)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_024204 else g32p_supplierForest_node_024258) else (if i.val < 147 then g32p_supplierForest_node_024277 else g32p_supplierForest_node_024302)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_024389 else g32p_supplierForest_node_024416) else (if i.val < 151 then g32p_supplierForest_node_024424 else g32p_supplierForest_node_024428))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_024442 else g32p_supplierForest_node_024519) else (if i.val < 155 then g32p_supplierForest_node_024554 else g32p_supplierForest_node_024667)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_024686 else g32p_supplierForest_node_024703) else (if i.val < 159 then g32p_supplierForest_node_024739 else g32p_supplierForest_node_024741))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_024795 else g32p_supplierForest_node_024843) else (if i.val < 163 then g32p_supplierForest_node_024870 else g32p_supplierForest_node_024883)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_024936 else g32p_supplierForest_node_024966) else (if i.val < 167 then g32p_supplierForest_node_025050 else g32p_supplierForest_node_025051))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_025063 else g32p_supplierForest_node_025090) else (if i.val < 171 then g32p_supplierForest_node_025138 else g32p_supplierForest_node_025159)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_025167 else g32p_supplierForest_node_025176) else (if i.val < 175 then g32p_supplierForest_node_025206 else g32p_supplierForest_node_025262)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_025271 else g32p_supplierForest_node_025278) else (if i.val < 179 then g32p_supplierForest_node_025312 else g32p_supplierForest_node_025314)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_025337 else g32p_supplierForest_node_025357) else (if i.val < 183 then g32p_supplierForest_node_025369 else g32p_supplierForest_node_025381))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_025398 else g32p_supplierForest_node_025404) else (if i.val < 187 then g32p_supplierForest_node_025555 else g32p_supplierForest_node_025559)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_025571 else g32p_supplierForest_node_025620) else (if i.val < 191 then g32p_supplierForest_node_025661 else g32p_supplierForest_node_025709)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_025795 else g32p_supplierForest_node_025958) else (if i.val < 195 then g32p_supplierForest_node_025984 else g32p_supplierForest_node_026068)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_026130 else g32p_supplierForest_node_026156) else (if i.val < 199 then g32p_supplierForest_node_026204 else g32p_supplierForest_node_026220))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_026273 else g32p_supplierForest_node_026325) else (if i.val < 203 then g32p_supplierForest_node_026398 else g32p_supplierForest_node_026433)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_026451 else g32p_supplierForest_node_026484) else (if i.val < 207 then g32p_supplierForest_node_026525 else g32p_supplierForest_node_026629)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_026656 else g32p_supplierForest_node_026668) else (if i.val < 211 then g32p_supplierForest_node_026689 else g32p_supplierForest_node_026755)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_026785 else g32p_supplierForest_node_026815) else (if i.val < 215 then g32p_supplierForest_node_026892 else g32p_supplierForest_node_026912))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_026955 else g32p_supplierForest_node_026970) else (if i.val < 219 then g32p_supplierForest_node_026972 else g32p_supplierForest_node_026973)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_027020 else g32p_supplierForest_node_027028) else (if i.val < 223 then g32p_supplierForest_node_027036 else g32p_supplierForest_node_027125))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_027133 else g32p_supplierForest_node_027154) else (if i.val < 227 then g32p_supplierForest_node_027159 else g32p_supplierForest_node_027204)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_027277 else g32p_supplierForest_node_027322) else (if i.val < 231 then g32p_supplierForest_node_027323 else g32p_supplierForest_node_027346))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_027352 else g32p_supplierForest_node_027415) else (if i.val < 235 then g32p_supplierForest_node_027416 else g32p_supplierForest_node_027418)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_027458 else g32p_supplierForest_node_027475) else (if i.val < 239 then g32p_supplierForest_node_027515 else g32p_supplierForest_node_027525)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_027528 else g32p_supplierForest_node_027536) else (if i.val < 243 then g32p_supplierForest_node_027548 else g32p_supplierForest_node_027581)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_027722 else g32p_supplierForest_node_027726) else (if i.val < 247 then g32p_supplierForest_node_027732 else g32p_supplierForest_node_027741))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_027773 else g32p_supplierForest_node_027776) else (if i.val < 251 then g32p_supplierForest_node_027777 else g32p_supplierForest_node_027805)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_027808 else g32p_supplierForest_node_027820) else (if i.val < 255 then g32p_supplierForest_node_027833 else g32p_supplierForest_node_027893))))))))

def g32p_supplierForest_classes_114 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 49 else 26) else (if i.val < 3 then 50 else 49)) else (if i.val < 6 then (if i.val < 5 then 10 else 25) else (if i.val < 7 then 27 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 50) else (if i.val < 11 then 49 else 27)) else (if i.val < 14 then (if i.val < 13 then 26 else 27) else (if i.val < 15 then 25 else 12)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 46 else 26) else (if i.val < 19 then 26 else 25)) else (if i.val < 22 then (if i.val < 21 then 47 else 27) else (if i.val < 23 then 10 else 25))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 27 else 27) else (if i.val < 27 then 27 else 10)) else (if i.val < 30 then (if i.val < 29 then 47 else 10) else (if i.val < 31 then 49 else 25))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 49 else 46) else (if i.val < 35 then 45 else 25)) else (if i.val < 38 then (if i.val < 37 then 26 else 49) else (if i.val < 39 then 25 else 27))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 47 else 49) else (if i.val < 43 then 27 else 46)) else (if i.val < 46 then (if i.val < 45 then 49 else 49) else (if i.val < 47 then 49 else 49)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 49) else (if i.val < 51 then 50 else 49)) else (if i.val < 54 then (if i.val < 53 then 12 else 49) else (if i.val < 55 then 56 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 50) else (if i.val < 59 then 49 else 46)) else (if i.val < 62 then (if i.val < 61 then 49 else 47) else (if i.val < 63 then 9 else 12)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 49) else (if i.val < 67 then 26 else 46)) else (if i.val < 70 then (if i.val < 69 then 27 else 49) else (if i.val < 71 then 49 else 48))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 9 else 26) else (if i.val < 75 then 50 else 49)) else (if i.val < 78 then (if i.val < 77 then 49 else 49) else (if i.val < 79 then 49 else 47)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 49 else 49) else (if i.val < 83 then 49 else 25)) else (if i.val < 86 then (if i.val < 85 then 9 else 12) else (if i.val < 87 then 10 else 46))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 26 else 49) else (if i.val < 91 then 49 else 47)) else (if i.val < 94 then (if i.val < 93 then 50 else 49) else (if i.val < 95 then 12 else 46))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 46 else 50) else (if i.val < 99 then 27 else 46)) else (if i.val < 102 then (if i.val < 101 then 12 else 9) else (if i.val < 103 then 26 else 49))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 49 else 12) else (if i.val < 107 then 47 else 50)) else (if i.val < 110 then (if i.val < 109 then 47 else 48) else (if i.val < 111 then 25 else 47)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 26 else 49) else (if i.val < 115 then 48 else 49)) else (if i.val < 118 then (if i.val < 117 then 46 else 26) else (if i.val < 119 then 49 else 50))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 54 else 26) else (if i.val < 123 then 25 else 50)) else (if i.val < 126 then (if i.val < 125 then 49 else 47) else (if i.val < 127 then 46 else 47))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 49) else (if i.val < 131 then 47 else 25)) else (if i.val < 134 then (if i.val < 133 then 25 else 49) else (if i.val < 135 then 27 else 26))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 49 else 49) else (if i.val < 139 then 49 else 50)) else (if i.val < 142 then (if i.val < 141 then 49 else 49) else (if i.val < 143 then 9 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 49 else 9) else (if i.val < 147 then 10 else 27)) else (if i.val < 150 then (if i.val < 149 then 9 else 46) else (if i.val < 151 then 49 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 27 else 30) else (if i.val < 155 then 16 else 15)) else (if i.val < 158 then (if i.val < 157 then 29 else 57) else (if i.val < 159 then 30 else 57))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 30 else 62) else (if i.val < 163 then 57 else 15)) else (if i.val < 166 then (if i.val < 165 then 17 else 14) else (if i.val < 167 then 15 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 57 else 33) else (if i.val < 171 then 15 else 58)) else (if i.val < 174 then (if i.val < 173 then 57 else 58) else (if i.val < 175 then 59 else 16)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 16 else 57) else (if i.val < 179 then 59 else 57)) else (if i.val < 182 then (if i.val < 181 then 58 else 30) else (if i.val < 183 then 16 else 29))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 33) else (if i.val < 187 then 15 else 15)) else (if i.val < 190 then (if i.val < 189 then 57 else 57) else (if i.val < 191 then 57 else 16)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 15) else (if i.val < 195 then 35 else 15)) else (if i.val < 198 then (if i.val < 197 then 32 else 29) else (if i.val < 199 then 16 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 14 else 57) else (if i.val < 203 then 30 else 15)) else (if i.val < 206 then (if i.val < 205 then 60 else 16) else (if i.val < 207 then 29 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 58 else 57) else (if i.val < 211 then 33 else 57)) else (if i.val < 214 then (if i.val < 213 then 30 else 57) else (if i.val < 215 then 57 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 30 else 16) else (if i.val < 219 then 14 else 30)) else (if i.val < 222 then (if i.val < 221 then 57 else 57) else (if i.val < 223 then 15 else 30))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 30) else (if i.val < 227 then 30 else 30)) else (if i.val < 230 then (if i.val < 229 then 30 else 57) else (if i.val < 231 then 59 else 16))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 57) else (if i.val < 235 then 57 else 57)) else (if i.val < 238 then (if i.val < 237 then 16 else 35) else (if i.val < 239 then 57 else 57)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 59 else 59) else (if i.val < 243 then 29 else 15)) else (if i.val < 246 then (if i.val < 245 then 30 else 30) else (if i.val < 247 then 17 else 57))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 16 else 30) else (if i.val < 251 then 14 else 14)) else (if i.val < 254 then (if i.val < 253 then 57 else 57) else (if i.val < 255 then 14 else 36))))))))

theorem g32p_supplierForest_actual_114 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_114 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_114 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_019666
  · exact g32p_supplierForest_actual_019682
  · exact g32p_supplierForest_actual_019689
  · exact g32p_supplierForest_actual_019691
  · exact g32p_supplierForest_actual_019699
  · exact g32p_supplierForest_actual_019744
  · exact g32p_supplierForest_actual_019746
  · exact g32p_supplierForest_actual_019762
  · exact g32p_supplierForest_actual_019873
  · exact g32p_supplierForest_actual_019923
  · exact g32p_supplierForest_actual_019933
  · exact g32p_supplierForest_actual_019934
  · exact g32p_supplierForest_actual_019966
  · exact g32p_supplierForest_actual_019992
  · exact g32p_supplierForest_actual_019996
  · exact g32p_supplierForest_actual_020083
  · exact g32p_supplierForest_actual_020106
  · exact g32p_supplierForest_actual_020111
  · exact g32p_supplierForest_actual_020116
  · exact g32p_supplierForest_actual_020163
  · exact g32p_supplierForest_actual_020193
  · exact g32p_supplierForest_actual_020222
  · exact g32p_supplierForest_actual_020226
  · exact g32p_supplierForest_actual_020289
  · exact g32p_supplierForest_actual_020296
  · exact g32p_supplierForest_actual_020353
  · exact g32p_supplierForest_actual_020389
  · exact g32p_supplierForest_actual_020407
  · exact g32p_supplierForest_actual_020485
  · exact g32p_supplierForest_actual_020500
  · exact g32p_supplierForest_actual_020526
  · exact g32p_supplierForest_actual_020552
  · exact g32p_supplierForest_actual_020670
  · exact g32p_supplierForest_actual_020726
  · exact g32p_supplierForest_actual_020767
  · exact g32p_supplierForest_actual_020770
  · exact g32p_supplierForest_actual_020819
  · exact g32p_supplierForest_actual_020832
  · exact g32p_supplierForest_actual_020869
  · exact g32p_supplierForest_actual_020897
  · exact g32p_supplierForest_actual_020902
  · exact g32p_supplierForest_actual_020945
  · exact g32p_supplierForest_actual_020984
  · exact g32p_supplierForest_actual_020988
  · exact g32p_supplierForest_actual_021066
  · exact g32p_supplierForest_actual_021083
  · exact g32p_supplierForest_actual_021087
  · exact g32p_supplierForest_actual_021114
  · exact g32p_supplierForest_actual_021153
  · exact g32p_supplierForest_actual_021185
  · exact g32p_supplierForest_actual_021186
  · exact g32p_supplierForest_actual_021240
  · exact g32p_supplierForest_actual_021288
  · exact g32p_supplierForest_actual_021307
  · exact g32p_supplierForest_actual_021327
  · exact g32p_supplierForest_actual_021349
  · exact g32p_supplierForest_actual_021353
  · exact g32p_supplierForest_actual_021356
  · exact g32p_supplierForest_actual_021376
  · exact g32p_supplierForest_actual_021396
  · exact g32p_supplierForest_actual_021442
  · exact g32p_supplierForest_actual_021471
  · exact g32p_supplierForest_actual_021523
  · exact g32p_supplierForest_actual_021551
  · exact g32p_supplierForest_actual_021606
  · exact g32p_supplierForest_actual_021653
  · exact g32p_supplierForest_actual_021795
  · exact g32p_supplierForest_actual_021828
  · exact g32p_supplierForest_actual_021958
  · exact g32p_supplierForest_actual_022011
  · exact g32p_supplierForest_actual_022012
  · exact g32p_supplierForest_actual_022035
  · exact g32p_supplierForest_actual_022109
  · exact g32p_supplierForest_actual_022146
  · exact g32p_supplierForest_actual_022174
  · exact g32p_supplierForest_actual_022178
  · exact g32p_supplierForest_actual_022204
  · exact g32p_supplierForest_actual_022247
  · exact g32p_supplierForest_actual_022272
  · exact g32p_supplierForest_actual_022345
  · exact g32p_supplierForest_actual_022354
  · exact g32p_supplierForest_actual_022366
  · exact g32p_supplierForest_actual_022372
  · exact g32p_supplierForest_actual_022403
  · exact g32p_supplierForest_actual_022428
  · exact g32p_supplierForest_actual_022430
  · exact g32p_supplierForest_actual_022467
  · exact g32p_supplierForest_actual_022492
  · exact g32p_supplierForest_actual_022496
  · exact g32p_supplierForest_actual_022509
  · exact g32p_supplierForest_actual_022525
  · exact g32p_supplierForest_actual_022564
  · exact g32p_supplierForest_actual_022594
  · exact g32p_supplierForest_actual_022614
  · exact g32p_supplierForest_actual_022673
  · exact g32p_supplierForest_actual_022676
  · exact g32p_supplierForest_actual_022682
  · exact g32p_supplierForest_actual_022698
  · exact g32p_supplierForest_actual_022737
  · exact g32p_supplierForest_actual_022807
  · exact g32p_supplierForest_actual_022812
  · exact g32p_supplierForest_actual_022846
  · exact g32p_supplierForest_actual_022877
  · exact g32p_supplierForest_actual_022889
  · exact g32p_supplierForest_actual_022900
  · exact g32p_supplierForest_actual_022904
  · exact g32p_supplierForest_actual_022944
  · exact g32p_supplierForest_actual_022949
  · exact g32p_supplierForest_actual_022989
  · exact g32p_supplierForest_actual_022999
  · exact g32p_supplierForest_actual_023018
  · exact g32p_supplierForest_actual_023033
  · exact g32p_supplierForest_actual_023036
  · exact g32p_supplierForest_actual_023104
  · exact g32p_supplierForest_actual_023186
  · exact g32p_supplierForest_actual_023201
  · exact g32p_supplierForest_actual_023234
  · exact g32p_supplierForest_actual_023322
  · exact g32p_supplierForest_actual_023370
  · exact g32p_supplierForest_actual_023435
  · exact g32p_supplierForest_actual_023499
  · exact g32p_supplierForest_actual_023528
  · exact g32p_supplierForest_actual_023532
  · exact g32p_supplierForest_actual_023588
  · exact g32p_supplierForest_actual_023589
  · exact g32p_supplierForest_actual_023615
  · exact g32p_supplierForest_actual_023624
  · exact g32p_supplierForest_actual_023631
  · exact g32p_supplierForest_actual_023655
  · exact g32p_supplierForest_actual_023678
  · exact g32p_supplierForest_actual_023709
  · exact g32p_supplierForest_actual_023714
  · exact g32p_supplierForest_actual_023728
  · exact g32p_supplierForest_actual_023797
  · exact g32p_supplierForest_actual_023798
  · exact g32p_supplierForest_actual_023964
  · exact g32p_supplierForest_actual_023990
  · exact g32p_supplierForest_actual_024000
  · exact g32p_supplierForest_actual_024001
  · exact g32p_supplierForest_actual_024007
  · exact g32p_supplierForest_actual_024025
  · exact g32p_supplierForest_actual_024123
  · exact g32p_supplierForest_actual_024154
  · exact g32p_supplierForest_actual_024168
  · exact g32p_supplierForest_actual_024204
  · exact g32p_supplierForest_actual_024258
  · exact g32p_supplierForest_actual_024277
  · exact g32p_supplierForest_actual_024302
  · exact g32p_supplierForest_actual_024389
  · exact g32p_supplierForest_actual_024416
  · exact g32p_supplierForest_actual_024424
  · exact g32p_supplierForest_actual_024428
  · exact g32p_supplierForest_actual_024442
  · exact g32p_supplierForest_actual_024519
  · exact g32p_supplierForest_actual_024554
  · exact g32p_supplierForest_actual_024667
  · exact g32p_supplierForest_actual_024686
  · exact g32p_supplierForest_actual_024703
  · exact g32p_supplierForest_actual_024739
  · exact g32p_supplierForest_actual_024741
  · exact g32p_supplierForest_actual_024795
  · exact g32p_supplierForest_actual_024843
  · exact g32p_supplierForest_actual_024870
  · exact g32p_supplierForest_actual_024883
  · exact g32p_supplierForest_actual_024936
  · exact g32p_supplierForest_actual_024966
  · exact g32p_supplierForest_actual_025050
  · exact g32p_supplierForest_actual_025051
  · exact g32p_supplierForest_actual_025063
  · exact g32p_supplierForest_actual_025090
  · exact g32p_supplierForest_actual_025138
  · exact g32p_supplierForest_actual_025159
  · exact g32p_supplierForest_actual_025167
  · exact g32p_supplierForest_actual_025176
  · exact g32p_supplierForest_actual_025206
  · exact g32p_supplierForest_actual_025262
  · exact g32p_supplierForest_actual_025271
  · exact g32p_supplierForest_actual_025278
  · exact g32p_supplierForest_actual_025312
  · exact g32p_supplierForest_actual_025314
  · exact g32p_supplierForest_actual_025337
  · exact g32p_supplierForest_actual_025357
  · exact g32p_supplierForest_actual_025369
  · exact g32p_supplierForest_actual_025381
  · exact g32p_supplierForest_actual_025398
  · exact g32p_supplierForest_actual_025404
  · exact g32p_supplierForest_actual_025555
  · exact g32p_supplierForest_actual_025559
  · exact g32p_supplierForest_actual_025571
  · exact g32p_supplierForest_actual_025620
  · exact g32p_supplierForest_actual_025661
  · exact g32p_supplierForest_actual_025709
  · exact g32p_supplierForest_actual_025795
  · exact g32p_supplierForest_actual_025958
  · exact g32p_supplierForest_actual_025984
  · exact g32p_supplierForest_actual_026068
  · exact g32p_supplierForest_actual_026130
  · exact g32p_supplierForest_actual_026156
  · exact g32p_supplierForest_actual_026204
  · exact g32p_supplierForest_actual_026220
  · exact g32p_supplierForest_actual_026273
  · exact g32p_supplierForest_actual_026325
  · exact g32p_supplierForest_actual_026398
  · exact g32p_supplierForest_actual_026433
  · exact g32p_supplierForest_actual_026451
  · exact g32p_supplierForest_actual_026484
  · exact g32p_supplierForest_actual_026525
  · exact g32p_supplierForest_actual_026629
  · exact g32p_supplierForest_actual_026656
  · exact g32p_supplierForest_actual_026668
  · exact g32p_supplierForest_actual_026689
  · exact g32p_supplierForest_actual_026755
  · exact g32p_supplierForest_actual_026785
  · exact g32p_supplierForest_actual_026815
  · exact g32p_supplierForest_actual_026892
  · exact g32p_supplierForest_actual_026912
  · exact g32p_supplierForest_actual_026955
  · exact g32p_supplierForest_actual_026970
  · exact g32p_supplierForest_actual_026972
  · exact g32p_supplierForest_actual_026973
  · exact g32p_supplierForest_actual_027020
  · exact g32p_supplierForest_actual_027028
  · exact g32p_supplierForest_actual_027036
  · exact g32p_supplierForest_actual_027125
  · exact g32p_supplierForest_actual_027133
  · exact g32p_supplierForest_actual_027154
  · exact g32p_supplierForest_actual_027159
  · exact g32p_supplierForest_actual_027204
  · exact g32p_supplierForest_actual_027277
  · exact g32p_supplierForest_actual_027322
  · exact g32p_supplierForest_actual_027323
  · exact g32p_supplierForest_actual_027346
  · exact g32p_supplierForest_actual_027352
  · exact g32p_supplierForest_actual_027415
  · exact g32p_supplierForest_actual_027416
  · exact g32p_supplierForest_actual_027418
  · exact g32p_supplierForest_actual_027458
  · exact g32p_supplierForest_actual_027475
  · exact g32p_supplierForest_actual_027515
  · exact g32p_supplierForest_actual_027525
  · exact g32p_supplierForest_actual_027528
  · exact g32p_supplierForest_actual_027536
  · exact g32p_supplierForest_actual_027548
  · exact g32p_supplierForest_actual_027581
  · exact g32p_supplierForest_actual_027722
  · exact g32p_supplierForest_actual_027726
  · exact g32p_supplierForest_actual_027732
  · exact g32p_supplierForest_actual_027741
  · exact g32p_supplierForest_actual_027773
  · exact g32p_supplierForest_actual_027776
  · exact g32p_supplierForest_actual_027777
  · exact g32p_supplierForest_actual_027805
  · exact g32p_supplierForest_actual_027808
  · exact g32p_supplierForest_actual_027820
  · exact g32p_supplierForest_actual_027833
  · exact g32p_supplierForest_actual_027893

def g32p_supplierForest_nodes_115 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_027918 else g32p_supplierForest_node_027923) else (if i.val < 3 then g32p_supplierForest_node_027976 else g32p_supplierForest_node_027993)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_028091 else g32p_supplierForest_node_028097) else (if i.val < 7 then g32p_supplierForest_node_028121 else g32p_supplierForest_node_028151))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_028171 else g32p_supplierForest_node_028174) else (if i.val < 11 then g32p_supplierForest_node_028235 else g32p_supplierForest_node_028329)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_028449 else g32p_supplierForest_node_028508) else (if i.val < 15 then g32p_supplierForest_node_028530 else g32p_supplierForest_node_028546)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_028598 else g32p_supplierForest_node_028600) else (if i.val < 19 then g32p_supplierForest_node_028644 else g32p_supplierForest_node_028702)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_028707 else g32p_supplierForest_node_028746) else (if i.val < 23 then g32p_supplierForest_node_028844 else g32p_supplierForest_node_028934))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_028953 else g32p_supplierForest_node_029011) else (if i.val < 27 then g32p_supplierForest_node_029024 else g32p_supplierForest_node_029060)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_029061 else g32p_supplierForest_node_029062) else (if i.val < 31 then g32p_supplierForest_node_029118 else g32p_supplierForest_node_029171))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_029212 else g32p_supplierForest_node_029271) else (if i.val < 35 then g32p_supplierForest_node_029280 else g32p_supplierForest_node_029328)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_029336 else g32p_supplierForest_node_029369) else (if i.val < 39 then g32p_supplierForest_node_029432 else g32p_supplierForest_node_029453))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_029483 else g32p_supplierForest_node_029518) else (if i.val < 43 then g32p_supplierForest_node_029522 else g32p_supplierForest_node_029536)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_029577 else g32p_supplierForest_node_029592) else (if i.val < 47 then g32p_supplierForest_node_029596 else g32p_supplierForest_node_029624)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_029684 else g32p_supplierForest_node_029721) else (if i.val < 51 then g32p_supplierForest_node_029728 else g32p_supplierForest_node_029760)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_029766 else g32p_supplierForest_node_029793) else (if i.val < 55 then g32p_supplierForest_node_029819 else g32p_supplierForest_node_029826))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_029857 else g32p_supplierForest_node_029886) else (if i.val < 59 then g32p_supplierForest_node_029930 else g32p_supplierForest_node_029968)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_029971 else g32p_supplierForest_node_029975) else (if i.val < 63 then g32p_supplierForest_node_030123 else g32p_supplierForest_node_030131)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_030193 else g32p_supplierForest_node_030195) else (if i.val < 67 then g32p_supplierForest_node_030234 else g32p_supplierForest_node_030236)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_030255 else g32p_supplierForest_node_030258) else (if i.val < 71 then g32p_supplierForest_node_030272 else g32p_supplierForest_node_030350))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_030362 else g32p_supplierForest_node_030368) else (if i.val < 75 then g32p_supplierForest_node_030401 else g32p_supplierForest_node_030462)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_030469 else g32p_supplierForest_node_030513) else (if i.val < 79 then g32p_supplierForest_node_030527 else g32p_supplierForest_node_030595)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_030642 else g32p_supplierForest_node_030643) else (if i.val < 83 then g32p_supplierForest_node_030663 else g32p_supplierForest_node_030759)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_030841 else g32p_supplierForest_node_030865) else (if i.val < 87 then g32p_supplierForest_node_030873 else g32p_supplierForest_node_030898))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_030905 else g32p_supplierForest_node_030907) else (if i.val < 91 then g32p_supplierForest_node_030913 else g32p_supplierForest_node_030919)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_030952 else g32p_supplierForest_node_030956) else (if i.val < 95 then g32p_supplierForest_node_031019 else g32p_supplierForest_node_031048))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_031089 else g32p_supplierForest_node_031092) else (if i.val < 99 then g32p_supplierForest_node_031102 else g32p_supplierForest_node_031106)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_031169 else g32p_supplierForest_node_031172) else (if i.val < 103 then g32p_supplierForest_node_031177 else g32p_supplierForest_node_031198))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_031248 else g32p_supplierForest_node_031253) else (if i.val < 107 then g32p_supplierForest_node_031262 else g32p_supplierForest_node_031365)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_031397 else g32p_supplierForest_node_031412) else (if i.val < 111 then g32p_supplierForest_node_031436 else g32p_supplierForest_node_031549)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_031638 else g32p_supplierForest_node_031758) else (if i.val < 115 then g32p_supplierForest_node_031784 else g32p_supplierForest_node_031839)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_031856 else g32p_supplierForest_node_031882) else (if i.val < 119 then g32p_supplierForest_node_031897 else g32p_supplierForest_node_031901))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_031934 else g32p_supplierForest_node_031977) else (if i.val < 123 then g32p_supplierForest_node_032028 else g32p_supplierForest_node_032062)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_032097 else g32p_supplierForest_node_032144) else (if i.val < 127 then g32p_supplierForest_node_032145 else g32p_supplierForest_node_032148))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_032158 else g32p_supplierForest_node_032192) else (if i.val < 131 then g32p_supplierForest_node_032202 else g32p_supplierForest_node_032216)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_032293 else g32p_supplierForest_node_032327) else (if i.val < 135 then g32p_supplierForest_node_032335 else g32p_supplierForest_node_032357))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_032384 else g32p_supplierForest_node_032407) else (if i.val < 139 then g32p_supplierForest_node_032410 else g32p_supplierForest_node_032415)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_032419 else g32p_supplierForest_node_032668) else (if i.val < 143 then g32p_supplierForest_node_032717 else g32p_supplierForest_node_032744)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_032758 else g32p_supplierForest_node_032780) else (if i.val < 147 then g32p_supplierForest_node_032799 else g32p_supplierForest_node_032826)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_032884 else g32p_supplierForest_node_032887) else (if i.val < 151 then g32p_supplierForest_node_032900 else g32p_supplierForest_node_032923))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_032926 else g32p_supplierForest_node_033007) else (if i.val < 155 then g32p_supplierForest_node_033036 else g32p_supplierForest_node_033079)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_033087 else g32p_supplierForest_node_033111) else (if i.val < 159 then g32p_supplierForest_node_033115 else g32p_supplierForest_node_033143))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_033154 else g32p_supplierForest_node_033174) else (if i.val < 163 then g32p_supplierForest_node_033213 else g32p_supplierForest_node_033217)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_033225 else g32p_supplierForest_node_033234) else (if i.val < 167 then g32p_supplierForest_node_033245 else g32p_supplierForest_node_033399))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_033428 else g32p_supplierForest_node_033437) else (if i.val < 171 then g32p_supplierForest_node_033461 else g32p_supplierForest_node_033484)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_033494 else g32p_supplierForest_node_033512) else (if i.val < 175 then g32p_supplierForest_node_033530 else g32p_supplierForest_node_033560)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_033564 else g32p_supplierForest_node_033609) else (if i.val < 179 then g32p_supplierForest_node_033619 else g32p_supplierForest_node_033653)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_033683 else g32p_supplierForest_node_033732) else (if i.val < 183 then g32p_supplierForest_node_033740 else g32p_supplierForest_node_033748))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_033768 else g32p_supplierForest_node_033829) else (if i.val < 187 then g32p_supplierForest_node_033856 else g32p_supplierForest_node_033874)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_033933 else g32p_supplierForest_node_033959) else (if i.val < 191 then g32p_supplierForest_node_033982 else g32p_supplierForest_node_034011)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_034015 else g32p_supplierForest_node_034148) else (if i.val < 195 then g32p_supplierForest_node_034162 else g32p_supplierForest_node_034169)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_034176 else g32p_supplierForest_node_034227) else (if i.val < 199 then g32p_supplierForest_node_034284 else g32p_supplierForest_node_034323))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_034326 else g32p_supplierForest_node_034370) else (if i.val < 203 then g32p_supplierForest_node_034397 else g32p_supplierForest_node_034438)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_034456 else g32p_supplierForest_node_034458) else (if i.val < 207 then g32p_supplierForest_node_034467 else g32p_supplierForest_node_034518)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_034625 else g32p_supplierForest_node_034659) else (if i.val < 211 then g32p_supplierForest_node_034676 else g32p_supplierForest_node_034707)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_034768 else g32p_supplierForest_node_034795) else (if i.val < 215 then g32p_supplierForest_node_034807 else g32p_supplierForest_node_034813))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_034816 else g32p_supplierForest_node_034838) else (if i.val < 219 then g32p_supplierForest_node_034854 else g32p_supplierForest_node_034896)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_034954 else g32p_supplierForest_node_034956) else (if i.val < 223 then g32p_supplierForest_node_035031 else g32p_supplierForest_node_035053))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_035054 else g32p_supplierForest_node_035058) else (if i.val < 227 then g32p_supplierForest_node_035098 else g32p_supplierForest_node_035173)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_035191 else g32p_supplierForest_node_035216) else (if i.val < 231 then g32p_supplierForest_node_035247 else g32p_supplierForest_node_035306))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_035349 else g32p_supplierForest_node_035357) else (if i.val < 235 then g32p_supplierForest_node_035387 else g32p_supplierForest_node_035424)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_035428 else g32p_supplierForest_node_035446) else (if i.val < 239 then g32p_supplierForest_node_035451 else g32p_supplierForest_node_035534)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_035563 else g32p_supplierForest_node_035626) else (if i.val < 243 then g32p_supplierForest_node_035628 else g32p_supplierForest_node_035665)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_035739 else g32p_supplierForest_node_035864) else (if i.val < 247 then g32p_supplierForest_node_035866 else g32p_supplierForest_node_035907))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_035909 else g32p_supplierForest_node_035920) else (if i.val < 251 then g32p_supplierForest_node_035923 else g32p_supplierForest_node_035975)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_035987 else g32p_supplierForest_node_036003) else (if i.val < 255 then g32p_supplierForest_node_036018 else g32p_supplierForest_node_036082))))))))

def g32p_supplierForest_classes_115 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 30 else 57) else (if i.val < 3 then 16 else 35)) else (if i.val < 6 then (if i.val < 5 then 57 else 57) else (if i.val < 7 then 57 else 17))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 30 else 59) else (if i.val < 11 then 16 else 16)) else (if i.val < 14 then (if i.val < 13 then 14 else 16) else (if i.val < 15 then 29 else 57)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 57 else 29) else (if i.val < 19 then 16 else 30)) else (if i.val < 22 then (if i.val < 21 then 62 else 16) else (if i.val < 23 then 17 else 30))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 57 else 30) else (if i.val < 27 then 16 else 57)) else (if i.val < 30 then (if i.val < 29 then 16 else 30) else (if i.val < 31 then 57 else 16))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 16 else 59) else (if i.val < 35 then 57 else 30)) else (if i.val < 38 then (if i.val < 37 then 63 else 17) else (if i.val < 39 then 57 else 30))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 15 else 16) else (if i.val < 43 then 14 else 57)) else (if i.val < 46 then (if i.val < 45 then 57 else 14) else (if i.val < 47 then 16 else 16)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 36 else 30) else (if i.val < 51 then 30 else 57)) else (if i.val < 54 then (if i.val < 53 then 15 else 57) else (if i.val < 55 then 57 else 30))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 29 else 30) else (if i.val < 59 then 57 else 57)) else (if i.val < 62 then (if i.val < 61 then 16 else 15) else (if i.val < 63 then 16 else 57)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 17 else 57) else (if i.val < 67 then 57 else 57)) else (if i.val < 70 then (if i.val < 69 then 16 else 59) else (if i.val < 71 then 57 else 57))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 30 else 61) else (if i.val < 75 then 14 else 57)) else (if i.val < 78 then (if i.val < 77 then 30 else 30) else (if i.val < 79 then 57 else 15)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 16 else 57) else (if i.val < 83 then 57 else 30)) else (if i.val < 86 then (if i.val < 85 then 30 else 57) else (if i.val < 87 then 15 else 59))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 30 else 30) else (if i.val < 91 then 57 else 57)) else (if i.val < 94 then (if i.val < 93 then 16 else 57) else (if i.val < 95 then 16 else 15))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 61 else 57) else (if i.val < 99 then 30 else 57)) else (if i.val < 102 then (if i.val < 101 then 57 else 63) else (if i.val < 103 then 63 else 30))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 30 else 30) else (if i.val < 107 then 57 else 16)) else (if i.val < 110 then (if i.val < 109 then 63 else 16) else (if i.val < 111 then 57 else 63)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 16 else 63) else (if i.val < 115 then 30 else 57)) else (if i.val < 118 then (if i.val < 117 then 32 else 62) else (if i.val < 119 then 32 else 29))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 30 else 16) else (if i.val < 123 then 16 else 63)) else (if i.val < 126 then (if i.val < 125 then 57 else 57) else (if i.val < 127 then 58 else 61))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 29 else 14) else (if i.val < 131 then 58 else 57)) else (if i.val < 134 then (if i.val < 133 then 57 else 30) else (if i.val < 135 then 63 else 16))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 16 else 30) else (if i.val < 139 then 33 else 16)) else (if i.val < 142 then (if i.val < 141 then 57 else 57) else (if i.val < 143 then 29 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 59 else 57) else (if i.val < 147 then 15 else 57)) else (if i.val < 150 then (if i.val < 149 then 57 else 57) else (if i.val < 151 then 59 else 14))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 30 else 30) else (if i.val < 155 then 16 else 29)) else (if i.val < 158 then (if i.val < 157 then 15 else 30) else (if i.val < 159 then 57 else 36))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 17 else 16) else (if i.val < 163 then 57 else 57)) else (if i.val < 166 then (if i.val < 165 then 57 else 33) else (if i.val < 167 then 62 else 16))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 61 else 61) else (if i.val < 171 then 30 else 16)) else (if i.val < 174 then (if i.val < 173 then 30 else 14) else (if i.val < 175 then 59 else 57)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 15 else 16) else (if i.val < 179 then 57 else 17)) else (if i.val < 182 then (if i.val < 181 then 57 else 58) else (if i.val < 183 then 30 else 16))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 58) else (if i.val < 187 then 16 else 57)) else (if i.val < 190 then (if i.val < 189 then 30 else 59) else (if i.val < 191 then 30 else 14)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 30 else 57) else (if i.val < 195 then 59 else 30)) else (if i.val < 198 then (if i.val < 197 then 57 else 17) else (if i.val < 199 then 30 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 57 else 30) else (if i.val < 203 then 57 else 30)) else (if i.val < 206 then (if i.val < 205 then 29 else 57) else (if i.val < 207 then 57 else 15)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 57 else 29) else (if i.val < 211 then 57 else 57)) else (if i.val < 214 then (if i.val < 213 then 57 else 60) else (if i.val < 215 then 35 else 30))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 57) else (if i.val < 219 then 30 else 57)) else (if i.val < 222 then (if i.val < 221 then 57 else 16) else (if i.val < 223 then 57 else 16))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 63 else 57) else (if i.val < 227 then 60 else 63)) else (if i.val < 230 then (if i.val < 229 then 59 else 14) else (if i.val < 231 then 14 else 16))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 57 else 15) else (if i.val < 235 then 30 else 33)) else (if i.val < 238 then (if i.val < 237 then 16 else 57) else (if i.val < 239 then 14 else 57)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 16 else 16) else (if i.val < 243 then 63 else 16)) else (if i.val < 246 then (if i.val < 245 then 16 else 62) else (if i.val < 247 then 17 else 16))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 14 else 33) else (if i.val < 251 then 57 else 30)) else (if i.val < 254 then (if i.val < 253 then 57 else 30) else (if i.val < 255 then 30 else 30))))))))

theorem g32p_supplierForest_actual_115 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_115 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_115 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_027918
  · exact g32p_supplierForest_actual_027923
  · exact g32p_supplierForest_actual_027976
  · exact g32p_supplierForest_actual_027993
  · exact g32p_supplierForest_actual_028091
  · exact g32p_supplierForest_actual_028097
  · exact g32p_supplierForest_actual_028121
  · exact g32p_supplierForest_actual_028151
  · exact g32p_supplierForest_actual_028171
  · exact g32p_supplierForest_actual_028174
  · exact g32p_supplierForest_actual_028235
  · exact g32p_supplierForest_actual_028329
  · exact g32p_supplierForest_actual_028449
  · exact g32p_supplierForest_actual_028508
  · exact g32p_supplierForest_actual_028530
  · exact g32p_supplierForest_actual_028546
  · exact g32p_supplierForest_actual_028598
  · exact g32p_supplierForest_actual_028600
  · exact g32p_supplierForest_actual_028644
  · exact g32p_supplierForest_actual_028702
  · exact g32p_supplierForest_actual_028707
  · exact g32p_supplierForest_actual_028746
  · exact g32p_supplierForest_actual_028844
  · exact g32p_supplierForest_actual_028934
  · exact g32p_supplierForest_actual_028953
  · exact g32p_supplierForest_actual_029011
  · exact g32p_supplierForest_actual_029024
  · exact g32p_supplierForest_actual_029060
  · exact g32p_supplierForest_actual_029061
  · exact g32p_supplierForest_actual_029062
  · exact g32p_supplierForest_actual_029118
  · exact g32p_supplierForest_actual_029171
  · exact g32p_supplierForest_actual_029212
  · exact g32p_supplierForest_actual_029271
  · exact g32p_supplierForest_actual_029280
  · exact g32p_supplierForest_actual_029328
  · exact g32p_supplierForest_actual_029336
  · exact g32p_supplierForest_actual_029369
  · exact g32p_supplierForest_actual_029432
  · exact g32p_supplierForest_actual_029453
  · exact g32p_supplierForest_actual_029483
  · exact g32p_supplierForest_actual_029518
  · exact g32p_supplierForest_actual_029522
  · exact g32p_supplierForest_actual_029536
  · exact g32p_supplierForest_actual_029577
  · exact g32p_supplierForest_actual_029592
  · exact g32p_supplierForest_actual_029596
  · exact g32p_supplierForest_actual_029624
  · exact g32p_supplierForest_actual_029684
  · exact g32p_supplierForest_actual_029721
  · exact g32p_supplierForest_actual_029728
  · exact g32p_supplierForest_actual_029760
  · exact g32p_supplierForest_actual_029766
  · exact g32p_supplierForest_actual_029793
  · exact g32p_supplierForest_actual_029819
  · exact g32p_supplierForest_actual_029826
  · exact g32p_supplierForest_actual_029857
  · exact g32p_supplierForest_actual_029886
  · exact g32p_supplierForest_actual_029930
  · exact g32p_supplierForest_actual_029968
  · exact g32p_supplierForest_actual_029971
  · exact g32p_supplierForest_actual_029975
  · exact g32p_supplierForest_actual_030123
  · exact g32p_supplierForest_actual_030131
  · exact g32p_supplierForest_actual_030193
  · exact g32p_supplierForest_actual_030195
  · exact g32p_supplierForest_actual_030234
  · exact g32p_supplierForest_actual_030236
  · exact g32p_supplierForest_actual_030255
  · exact g32p_supplierForest_actual_030258
  · exact g32p_supplierForest_actual_030272
  · exact g32p_supplierForest_actual_030350
  · exact g32p_supplierForest_actual_030362
  · exact g32p_supplierForest_actual_030368
  · exact g32p_supplierForest_actual_030401
  · exact g32p_supplierForest_actual_030462
  · exact g32p_supplierForest_actual_030469
  · exact g32p_supplierForest_actual_030513
  · exact g32p_supplierForest_actual_030527
  · exact g32p_supplierForest_actual_030595
  · exact g32p_supplierForest_actual_030642
  · exact g32p_supplierForest_actual_030643
  · exact g32p_supplierForest_actual_030663
  · exact g32p_supplierForest_actual_030759
  · exact g32p_supplierForest_actual_030841
  · exact g32p_supplierForest_actual_030865
  · exact g32p_supplierForest_actual_030873
  · exact g32p_supplierForest_actual_030898
  · exact g32p_supplierForest_actual_030905
  · exact g32p_supplierForest_actual_030907
  · exact g32p_supplierForest_actual_030913
  · exact g32p_supplierForest_actual_030919
  · exact g32p_supplierForest_actual_030952
  · exact g32p_supplierForest_actual_030956
  · exact g32p_supplierForest_actual_031019
  · exact g32p_supplierForest_actual_031048
  · exact g32p_supplierForest_actual_031089
  · exact g32p_supplierForest_actual_031092
  · exact g32p_supplierForest_actual_031102
  · exact g32p_supplierForest_actual_031106
  · exact g32p_supplierForest_actual_031169
  · exact g32p_supplierForest_actual_031172
  · exact g32p_supplierForest_actual_031177
  · exact g32p_supplierForest_actual_031198
  · exact g32p_supplierForest_actual_031248
  · exact g32p_supplierForest_actual_031253
  · exact g32p_supplierForest_actual_031262
  · exact g32p_supplierForest_actual_031365
  · exact g32p_supplierForest_actual_031397
  · exact g32p_supplierForest_actual_031412
  · exact g32p_supplierForest_actual_031436
  · exact g32p_supplierForest_actual_031549
  · exact g32p_supplierForest_actual_031638
  · exact g32p_supplierForest_actual_031758
  · exact g32p_supplierForest_actual_031784
  · exact g32p_supplierForest_actual_031839
  · exact g32p_supplierForest_actual_031856
  · exact g32p_supplierForest_actual_031882
  · exact g32p_supplierForest_actual_031897
  · exact g32p_supplierForest_actual_031901
  · exact g32p_supplierForest_actual_031934
  · exact g32p_supplierForest_actual_031977
  · exact g32p_supplierForest_actual_032028
  · exact g32p_supplierForest_actual_032062
  · exact g32p_supplierForest_actual_032097
  · exact g32p_supplierForest_actual_032144
  · exact g32p_supplierForest_actual_032145
  · exact g32p_supplierForest_actual_032148
  · exact g32p_supplierForest_actual_032158
  · exact g32p_supplierForest_actual_032192
  · exact g32p_supplierForest_actual_032202
  · exact g32p_supplierForest_actual_032216
  · exact g32p_supplierForest_actual_032293
  · exact g32p_supplierForest_actual_032327
  · exact g32p_supplierForest_actual_032335
  · exact g32p_supplierForest_actual_032357
  · exact g32p_supplierForest_actual_032384
  · exact g32p_supplierForest_actual_032407
  · exact g32p_supplierForest_actual_032410
  · exact g32p_supplierForest_actual_032415
  · exact g32p_supplierForest_actual_032419
  · exact g32p_supplierForest_actual_032668
  · exact g32p_supplierForest_actual_032717
  · exact g32p_supplierForest_actual_032744
  · exact g32p_supplierForest_actual_032758
  · exact g32p_supplierForest_actual_032780
  · exact g32p_supplierForest_actual_032799
  · exact g32p_supplierForest_actual_032826
  · exact g32p_supplierForest_actual_032884
  · exact g32p_supplierForest_actual_032887
  · exact g32p_supplierForest_actual_032900
  · exact g32p_supplierForest_actual_032923
  · exact g32p_supplierForest_actual_032926
  · exact g32p_supplierForest_actual_033007
  · exact g32p_supplierForest_actual_033036
  · exact g32p_supplierForest_actual_033079
  · exact g32p_supplierForest_actual_033087
  · exact g32p_supplierForest_actual_033111
  · exact g32p_supplierForest_actual_033115
  · exact g32p_supplierForest_actual_033143
  · exact g32p_supplierForest_actual_033154
  · exact g32p_supplierForest_actual_033174
  · exact g32p_supplierForest_actual_033213
  · exact g32p_supplierForest_actual_033217
  · exact g32p_supplierForest_actual_033225
  · exact g32p_supplierForest_actual_033234
  · exact g32p_supplierForest_actual_033245
  · exact g32p_supplierForest_actual_033399
  · exact g32p_supplierForest_actual_033428
  · exact g32p_supplierForest_actual_033437
  · exact g32p_supplierForest_actual_033461
  · exact g32p_supplierForest_actual_033484
  · exact g32p_supplierForest_actual_033494
  · exact g32p_supplierForest_actual_033512
  · exact g32p_supplierForest_actual_033530
  · exact g32p_supplierForest_actual_033560
  · exact g32p_supplierForest_actual_033564
  · exact g32p_supplierForest_actual_033609
  · exact g32p_supplierForest_actual_033619
  · exact g32p_supplierForest_actual_033653
  · exact g32p_supplierForest_actual_033683
  · exact g32p_supplierForest_actual_033732
  · exact g32p_supplierForest_actual_033740
  · exact g32p_supplierForest_actual_033748
  · exact g32p_supplierForest_actual_033768
  · exact g32p_supplierForest_actual_033829
  · exact g32p_supplierForest_actual_033856
  · exact g32p_supplierForest_actual_033874
  · exact g32p_supplierForest_actual_033933
  · exact g32p_supplierForest_actual_033959
  · exact g32p_supplierForest_actual_033982
  · exact g32p_supplierForest_actual_034011
  · exact g32p_supplierForest_actual_034015
  · exact g32p_supplierForest_actual_034148
  · exact g32p_supplierForest_actual_034162
  · exact g32p_supplierForest_actual_034169
  · exact g32p_supplierForest_actual_034176
  · exact g32p_supplierForest_actual_034227
  · exact g32p_supplierForest_actual_034284
  · exact g32p_supplierForest_actual_034323
  · exact g32p_supplierForest_actual_034326
  · exact g32p_supplierForest_actual_034370
  · exact g32p_supplierForest_actual_034397
  · exact g32p_supplierForest_actual_034438
  · exact g32p_supplierForest_actual_034456
  · exact g32p_supplierForest_actual_034458
  · exact g32p_supplierForest_actual_034467
  · exact g32p_supplierForest_actual_034518
  · exact g32p_supplierForest_actual_034625
  · exact g32p_supplierForest_actual_034659
  · exact g32p_supplierForest_actual_034676
  · exact g32p_supplierForest_actual_034707
  · exact g32p_supplierForest_actual_034768
  · exact g32p_supplierForest_actual_034795
  · exact g32p_supplierForest_actual_034807
  · exact g32p_supplierForest_actual_034813
  · exact g32p_supplierForest_actual_034816
  · exact g32p_supplierForest_actual_034838
  · exact g32p_supplierForest_actual_034854
  · exact g32p_supplierForest_actual_034896
  · exact g32p_supplierForest_actual_034954
  · exact g32p_supplierForest_actual_034956
  · exact g32p_supplierForest_actual_035031
  · exact g32p_supplierForest_actual_035053
  · exact g32p_supplierForest_actual_035054
  · exact g32p_supplierForest_actual_035058
  · exact g32p_supplierForest_actual_035098
  · exact g32p_supplierForest_actual_035173
  · exact g32p_supplierForest_actual_035191
  · exact g32p_supplierForest_actual_035216
  · exact g32p_supplierForest_actual_035247
  · exact g32p_supplierForest_actual_035306
  · exact g32p_supplierForest_actual_035349
  · exact g32p_supplierForest_actual_035357
  · exact g32p_supplierForest_actual_035387
  · exact g32p_supplierForest_actual_035424
  · exact g32p_supplierForest_actual_035428
  · exact g32p_supplierForest_actual_035446
  · exact g32p_supplierForest_actual_035451
  · exact g32p_supplierForest_actual_035534
  · exact g32p_supplierForest_actual_035563
  · exact g32p_supplierForest_actual_035626
  · exact g32p_supplierForest_actual_035628
  · exact g32p_supplierForest_actual_035665
  · exact g32p_supplierForest_actual_035739
  · exact g32p_supplierForest_actual_035864
  · exact g32p_supplierForest_actual_035866
  · exact g32p_supplierForest_actual_035907
  · exact g32p_supplierForest_actual_035909
  · exact g32p_supplierForest_actual_035920
  · exact g32p_supplierForest_actual_035923
  · exact g32p_supplierForest_actual_035975
  · exact g32p_supplierForest_actual_035987
  · exact g32p_supplierForest_actual_036003
  · exact g32p_supplierForest_actual_036018
  · exact g32p_supplierForest_actual_036082

def g32p_supplierForest_nodes_116 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_036143 else g32p_supplierForest_node_036206) else (if i.val < 3 then g32p_supplierForest_node_036297 else g32p_supplierForest_node_036337)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_036343 else g32p_supplierForest_node_036380) else (if i.val < 7 then g32p_supplierForest_node_036410 else g32p_supplierForest_node_036492))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_036542 else g32p_supplierForest_node_036548) else (if i.val < 11 then g32p_supplierForest_node_036587 else g32p_supplierForest_node_036601)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_036614 else g32p_supplierForest_node_036620) else (if i.val < 15 then g32p_supplierForest_node_036637 else g32p_supplierForest_node_036702)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_036724 else g32p_supplierForest_node_036753) else (if i.val < 19 then g32p_supplierForest_node_036762 else g32p_supplierForest_node_036780)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_036795 else g32p_supplierForest_node_036802) else (if i.val < 23 then g32p_supplierForest_node_036860 else g32p_supplierForest_node_036891))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_036955 else g32p_supplierForest_node_037065) else (if i.val < 27 then g32p_supplierForest_node_037079 else g32p_supplierForest_node_037109)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_037114 else g32p_supplierForest_node_037262) else (if i.val < 31 then g32p_supplierForest_node_037287 else g32p_supplierForest_node_037326))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_037355 else g32p_supplierForest_node_037365) else (if i.val < 35 then g32p_supplierForest_node_037401 else g32p_supplierForest_node_037418)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_037425 else g32p_supplierForest_node_037433) else (if i.val < 39 then g32p_supplierForest_node_037437 else g32p_supplierForest_node_037483))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_037529 else g32p_supplierForest_node_037530) else (if i.val < 43 then g32p_supplierForest_node_037531 else g32p_supplierForest_node_037648)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_037655 else g32p_supplierForest_node_037675) else (if i.val < 47 then g32p_supplierForest_node_037677 else g32p_supplierForest_node_037696)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_037726 else g32p_supplierForest_node_037765) else (if i.val < 51 then g32p_supplierForest_node_037856 else g32p_supplierForest_node_037869)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_037898 else g32p_supplierForest_node_037902) else (if i.val < 55 then g32p_supplierForest_node_037907 else g32p_supplierForest_node_037909))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_037930 else g32p_supplierForest_node_037968) else (if i.val < 59 then g32p_supplierForest_node_037986 else g32p_supplierForest_node_038029)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_038041 else g32p_supplierForest_node_038048) else (if i.val < 63 then g32p_supplierForest_node_038097 else g32p_supplierForest_node_038104)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_038112 else g32p_supplierForest_node_038117) else (if i.val < 67 then g32p_supplierForest_node_038186 else g32p_supplierForest_node_038187)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_038254 else g32p_supplierForest_node_038273) else (if i.val < 71 then g32p_supplierForest_node_038288 else g32p_supplierForest_node_038329))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_038334 else g32p_supplierForest_node_038351) else (if i.val < 75 then g32p_supplierForest_node_038352 else g32p_supplierForest_node_038398)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_038401 else g32p_supplierForest_node_038415) else (if i.val < 79 then g32p_supplierForest_node_038521 else g32p_supplierForest_node_038558)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_038608 else g32p_supplierForest_node_038650) else (if i.val < 83 then g32p_supplierForest_node_038697 else g32p_supplierForest_node_038701)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_038719 else g32p_supplierForest_node_038738) else (if i.val < 87 then g32p_supplierForest_node_038818 else g32p_supplierForest_node_038845))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_038885 else g32p_supplierForest_node_038893) else (if i.val < 91 then g32p_supplierForest_node_038909 else g32p_supplierForest_node_038917)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_038975 else g32p_supplierForest_node_038997) else (if i.val < 95 then g32p_supplierForest_node_039006 else g32p_supplierForest_node_039025))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_039031 else g32p_supplierForest_node_039035) else (if i.val < 99 then g32p_supplierForest_node_039132 else g32p_supplierForest_node_039154)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_039192 else g32p_supplierForest_node_039213) else (if i.val < 103 then g32p_supplierForest_node_039218 else g32p_supplierForest_node_039220))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_039299 else g32p_supplierForest_node_039313) else (if i.val < 107 then g32p_supplierForest_node_039338 else g32p_supplierForest_node_039356)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_039395 else g32p_supplierForest_node_039561) else (if i.val < 111 then g32p_supplierForest_node_039564 else g32p_supplierForest_node_039591)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_039630 else g32p_supplierForest_node_039663) else (if i.val < 115 then g32p_supplierForest_node_039686 else g32p_supplierForest_node_039713)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_039719 else g32p_supplierForest_node_039727) else (if i.val < 119 then g32p_supplierForest_node_039730 else g32p_supplierForest_node_039756))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_039806 else g32p_supplierForest_node_039811) else (if i.val < 123 then g32p_supplierForest_node_039814 else g32p_supplierForest_node_039829)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_039845 else g32p_supplierForest_node_039855) else (if i.val < 127 then g32p_supplierForest_node_039869 else g32p_supplierForest_node_039872))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_039915 else g32p_supplierForest_node_039929) else (if i.val < 131 then g32p_supplierForest_node_039950 else g32p_supplierForest_node_040011)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_040027 else g32p_supplierForest_node_040038) else (if i.val < 135 then g32p_supplierForest_node_040057 else g32p_supplierForest_node_040073))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_040075 else g32p_supplierForest_node_040076) else (if i.val < 139 then g32p_supplierForest_node_040082 else g32p_supplierForest_node_040103)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_040104 else g32p_supplierForest_node_040218) else (if i.val < 143 then g32p_supplierForest_node_040303 else g32p_supplierForest_node_040306)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_040328 else g32p_supplierForest_node_040372) else (if i.val < 147 then g32p_supplierForest_node_040404 else g32p_supplierForest_node_040444)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_040457 else g32p_supplierForest_node_040523) else (if i.val < 151 then g32p_supplierForest_node_040568 else g32p_supplierForest_node_040618))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_040740 else g32p_supplierForest_node_040762) else (if i.val < 155 then g32p_supplierForest_node_040773 else g32p_supplierForest_node_040774)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_040779 else g32p_supplierForest_node_040884) else (if i.val < 159 then g32p_supplierForest_node_040916 else g32p_supplierForest_node_040937))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_040954 else g32p_supplierForest_node_040987) else (if i.val < 163 then g32p_supplierForest_node_041008 else g32p_supplierForest_node_041058)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_041131 else g32p_supplierForest_node_041138) else (if i.val < 167 then g32p_supplierForest_node_041158 else g32p_supplierForest_node_041163))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_041203 else g32p_supplierForest_node_041225) else (if i.val < 171 then g32p_supplierForest_node_041365 else g32p_supplierForest_node_041396)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_041442 else g32p_supplierForest_node_041526) else (if i.val < 175 then g32p_supplierForest_node_041532 else g32p_supplierForest_node_041538)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_041557 else g32p_supplierForest_node_041560) else (if i.val < 179 then g32p_supplierForest_node_041564 else g32p_supplierForest_node_041568)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_041594 else g32p_supplierForest_node_041600) else (if i.val < 183 then g32p_supplierForest_node_041695 else g32p_supplierForest_node_041728))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_041735 else g32p_supplierForest_node_041774) else (if i.val < 187 then g32p_supplierForest_node_041811 else g32p_supplierForest_node_041819)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_041842 else g32p_supplierForest_node_041855) else (if i.val < 191 then g32p_supplierForest_node_041871 else g32p_supplierForest_node_041941)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_041972 else g32p_supplierForest_node_041986) else (if i.val < 195 then g32p_supplierForest_node_042009 else g32p_supplierForest_node_042010)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_042139 else g32p_supplierForest_node_042147) else (if i.val < 199 then g32p_supplierForest_node_042148 else g32p_supplierForest_node_042225))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_042229 else g32p_supplierForest_node_042262) else (if i.val < 203 then g32p_supplierForest_node_042290 else g32p_supplierForest_node_042313)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_042378 else g32p_supplierForest_node_042394) else (if i.val < 207 then g32p_supplierForest_node_042427 else g32p_supplierForest_node_042488)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_042561 else g32p_supplierForest_node_042563) else (if i.val < 211 then g32p_supplierForest_node_042577 else g32p_supplierForest_node_042629)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_042633 else g32p_supplierForest_node_042662) else (if i.val < 215 then g32p_supplierForest_node_042663 else g32p_supplierForest_node_042673))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_042727 else g32p_supplierForest_node_042770) else (if i.val < 219 then g32p_supplierForest_node_042777 else g32p_supplierForest_node_042825)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_042853 else g32p_supplierForest_node_042931) else (if i.val < 223 then g32p_supplierForest_node_042994 else g32p_supplierForest_node_043041))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_043043 else g32p_supplierForest_node_043086) else (if i.val < 227 then g32p_supplierForest_node_043148 else g32p_supplierForest_node_043178)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_043180 else g32p_supplierForest_node_043196) else (if i.val < 231 then g32p_supplierForest_node_043203 else g32p_supplierForest_node_043209))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_043212 else g32p_supplierForest_node_043282) else (if i.val < 235 then g32p_supplierForest_node_043347 else g32p_supplierForest_node_043349)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_043364 else g32p_supplierForest_node_043373) else (if i.val < 239 then g32p_supplierForest_node_043374 else g32p_supplierForest_node_043408)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_043510 else g32p_supplierForest_node_043520) else (if i.val < 243 then g32p_supplierForest_node_043572 else g32p_supplierForest_node_043605)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_043619 else g32p_supplierForest_node_043657) else (if i.val < 247 then g32p_supplierForest_node_043711 else g32p_supplierForest_node_043762))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_043779 else g32p_supplierForest_node_043817) else (if i.val < 251 then g32p_supplierForest_node_043828 else g32p_supplierForest_node_043834)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_043888 else g32p_supplierForest_node_043934) else (if i.val < 255 then g32p_supplierForest_node_043942 else g32p_supplierForest_node_043950))))))))

def g32p_supplierForest_classes_116 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 60) else (if i.val < 3 then 57 else 57)) else (if i.val < 6 then (if i.val < 5 then 57 else 16) else (if i.val < 7 then 57 else 57))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 30 else 57) else (if i.val < 11 then 30 else 57)) else (if i.val < 14 then (if i.val < 13 then 57 else 33) else (if i.val < 15 then 57 else 59)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 17 else 30) else (if i.val < 19 then 59 else 15)) else (if i.val < 22 then (if i.val < 21 then 33 else 57) else (if i.val < 23 then 57 else 57))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 15 else 57) else (if i.val < 27 then 30 else 57)) else (if i.val < 30 then (if i.val < 29 then 16 else 57) else (if i.val < 31 then 14 else 29))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 29 else 15) else (if i.val < 35 then 57 else 57)) else (if i.val < 38 then (if i.val < 37 then 30 else 32) else (if i.val < 39 then 16 else 15))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 35 else 30) else (if i.val < 43 then 29 else 30)) else (if i.val < 46 then (if i.val < 45 then 57 else 57) else (if i.val < 47 then 30 else 30)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 29 else 30) else (if i.val < 51 then 57 else 63)) else (if i.val < 54 then (if i.val < 53 then 15 else 30) else (if i.val < 55 then 29 else 15))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 29 else 17) else (if i.val < 59 then 57 else 57)) else (if i.val < 62 then (if i.val < 61 then 33 else 30) else (if i.val < 63 then 29 else 60)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 14 else 17) else (if i.val < 67 then 14 else 29)) else (if i.val < 70 then (if i.val < 69 then 29 else 29) else (if i.val < 71 then 62 else 16))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 16 else 30) else (if i.val < 75 then 66 else 57)) else (if i.val < 78 then (if i.val < 77 then 30 else 16) else (if i.val < 79 then 16 else 57)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 30 else 66) else (if i.val < 83 then 59 else 59)) else (if i.val < 86 then (if i.val < 85 then 57 else 30) else (if i.val < 87 then 57 else 57))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 60) else (if i.val < 91 then 57 else 30)) else (if i.val < 94 then (if i.val < 93 then 17 else 59) else (if i.val < 95 then 30 else 57))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 16 else 57) else (if i.val < 99 then 63 else 57)) else (if i.val < 102 then (if i.val < 101 then 57 else 62) else (if i.val < 103 then 16 else 57))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 63 else 57) else (if i.val < 107 then 36 else 57)) else (if i.val < 110 then (if i.val < 109 then 15 else 17) else (if i.val < 111 then 57 else 17)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 63 else 57) else (if i.val < 115 then 29 else 16)) else (if i.val < 118 then (if i.val < 117 then 57 else 59) else (if i.val < 119 then 63 else 30))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 57 else 63) else (if i.val < 123 then 16 else 30)) else (if i.val < 126 then (if i.val < 125 then 64 else 57) else (if i.val < 127 then 16 else 16))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 63 else 57) else (if i.val < 131 then 16 else 57)) else (if i.val < 134 then (if i.val < 133 then 16 else 30) else (if i.val < 135 then 57 else 59))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 57 else 57) else (if i.val < 139 then 15 else 30)) else (if i.val < 142 then (if i.val < 141 then 59 else 30) else (if i.val < 143 then 57 else 62)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 30 else 57) else (if i.val < 147 then 57 else 16)) else (if i.val < 150 then (if i.val < 149 then 30 else 36) else (if i.val < 151 then 30 else 57))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 30) else (if i.val < 155 then 30 else 57)) else (if i.val < 158 then (if i.val < 157 then 57 else 60) else (if i.val < 159 then 57 else 57))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 57 else 58) else (if i.val < 163 then 30 else 57)) else (if i.val < 166 then (if i.val < 165 then 57 else 57) else (if i.val < 167 then 14 else 17))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 30 else 59) else (if i.val < 171 then 14 else 60)) else (if i.val < 174 then (if i.val < 173 then 57 else 36) else (if i.val < 175 then 17 else 17)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 57 else 30) else (if i.val < 179 then 15 else 14)) else (if i.val < 182 then (if i.val < 181 then 14 else 30) else (if i.val < 183 then 15 else 57))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 16 else 63) else (if i.val < 187 then 32 else 57)) else (if i.val < 190 then (if i.val < 189 then 16 else 57) else (if i.val < 191 then 36 else 57)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 30) else (if i.val < 195 then 57 else 59)) else (if i.val < 198 then (if i.val < 197 then 30 else 30) else (if i.val < 199 then 62 else 30))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 30 else 57) else (if i.val < 203 then 30 else 35)) else (if i.val < 206 then (if i.val < 205 then 30 else 16) else (if i.val < 207 then 57 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 16 else 57) else (if i.val < 211 then 30 else 32)) else (if i.val < 214 then (if i.val < 213 then 57 else 59) else (if i.val < 215 then 14 else 16))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 59 else 57) else (if i.val < 219 then 57 else 33)) else (if i.val < 222 then (if i.val < 221 then 57 else 58) else (if i.val < 223 then 33 else 57))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 57) else (if i.val < 227 then 57 else 57)) else (if i.val < 230 then (if i.val < 229 then 60 else 66) else (if i.val < 231 then 30 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 36 else 16) else (if i.val < 235 then 57 else 14)) else (if i.val < 238 then (if i.val < 237 then 30 else 16) else (if i.val < 239 then 30 else 57)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 16) else (if i.val < 243 then 30 else 57)) else (if i.val < 246 then (if i.val < 245 then 59 else 64) else (if i.val < 247 then 63 else 16))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 30 else 30) else (if i.val < 251 then 57 else 30)) else (if i.val < 254 then (if i.val < 253 then 30 else 60) else (if i.val < 255 then 36 else 58))))))))

theorem g32p_supplierForest_actual_116 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_116 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_116 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_036143
  · exact g32p_supplierForest_actual_036206
  · exact g32p_supplierForest_actual_036297
  · exact g32p_supplierForest_actual_036337
  · exact g32p_supplierForest_actual_036343
  · exact g32p_supplierForest_actual_036380
  · exact g32p_supplierForest_actual_036410
  · exact g32p_supplierForest_actual_036492
  · exact g32p_supplierForest_actual_036542
  · exact g32p_supplierForest_actual_036548
  · exact g32p_supplierForest_actual_036587
  · exact g32p_supplierForest_actual_036601
  · exact g32p_supplierForest_actual_036614
  · exact g32p_supplierForest_actual_036620
  · exact g32p_supplierForest_actual_036637
  · exact g32p_supplierForest_actual_036702
  · exact g32p_supplierForest_actual_036724
  · exact g32p_supplierForest_actual_036753
  · exact g32p_supplierForest_actual_036762
  · exact g32p_supplierForest_actual_036780
  · exact g32p_supplierForest_actual_036795
  · exact g32p_supplierForest_actual_036802
  · exact g32p_supplierForest_actual_036860
  · exact g32p_supplierForest_actual_036891
  · exact g32p_supplierForest_actual_036955
  · exact g32p_supplierForest_actual_037065
  · exact g32p_supplierForest_actual_037079
  · exact g32p_supplierForest_actual_037109
  · exact g32p_supplierForest_actual_037114
  · exact g32p_supplierForest_actual_037262
  · exact g32p_supplierForest_actual_037287
  · exact g32p_supplierForest_actual_037326
  · exact g32p_supplierForest_actual_037355
  · exact g32p_supplierForest_actual_037365
  · exact g32p_supplierForest_actual_037401
  · exact g32p_supplierForest_actual_037418
  · exact g32p_supplierForest_actual_037425
  · exact g32p_supplierForest_actual_037433
  · exact g32p_supplierForest_actual_037437
  · exact g32p_supplierForest_actual_037483
  · exact g32p_supplierForest_actual_037529
  · exact g32p_supplierForest_actual_037530
  · exact g32p_supplierForest_actual_037531
  · exact g32p_supplierForest_actual_037648
  · exact g32p_supplierForest_actual_037655
  · exact g32p_supplierForest_actual_037675
  · exact g32p_supplierForest_actual_037677
  · exact g32p_supplierForest_actual_037696
  · exact g32p_supplierForest_actual_037726
  · exact g32p_supplierForest_actual_037765
  · exact g32p_supplierForest_actual_037856
  · exact g32p_supplierForest_actual_037869
  · exact g32p_supplierForest_actual_037898
  · exact g32p_supplierForest_actual_037902
  · exact g32p_supplierForest_actual_037907
  · exact g32p_supplierForest_actual_037909
  · exact g32p_supplierForest_actual_037930
  · exact g32p_supplierForest_actual_037968
  · exact g32p_supplierForest_actual_037986
  · exact g32p_supplierForest_actual_038029
  · exact g32p_supplierForest_actual_038041
  · exact g32p_supplierForest_actual_038048
  · exact g32p_supplierForest_actual_038097
  · exact g32p_supplierForest_actual_038104
  · exact g32p_supplierForest_actual_038112
  · exact g32p_supplierForest_actual_038117
  · exact g32p_supplierForest_actual_038186
  · exact g32p_supplierForest_actual_038187
  · exact g32p_supplierForest_actual_038254
  · exact g32p_supplierForest_actual_038273
  · exact g32p_supplierForest_actual_038288
  · exact g32p_supplierForest_actual_038329
  · exact g32p_supplierForest_actual_038334
  · exact g32p_supplierForest_actual_038351
  · exact g32p_supplierForest_actual_038352
  · exact g32p_supplierForest_actual_038398
  · exact g32p_supplierForest_actual_038401
  · exact g32p_supplierForest_actual_038415
  · exact g32p_supplierForest_actual_038521
  · exact g32p_supplierForest_actual_038558
  · exact g32p_supplierForest_actual_038608
  · exact g32p_supplierForest_actual_038650
  · exact g32p_supplierForest_actual_038697
  · exact g32p_supplierForest_actual_038701
  · exact g32p_supplierForest_actual_038719
  · exact g32p_supplierForest_actual_038738
  · exact g32p_supplierForest_actual_038818
  · exact g32p_supplierForest_actual_038845
  · exact g32p_supplierForest_actual_038885
  · exact g32p_supplierForest_actual_038893
  · exact g32p_supplierForest_actual_038909
  · exact g32p_supplierForest_actual_038917
  · exact g32p_supplierForest_actual_038975
  · exact g32p_supplierForest_actual_038997
  · exact g32p_supplierForest_actual_039006
  · exact g32p_supplierForest_actual_039025
  · exact g32p_supplierForest_actual_039031
  · exact g32p_supplierForest_actual_039035
  · exact g32p_supplierForest_actual_039132
  · exact g32p_supplierForest_actual_039154
  · exact g32p_supplierForest_actual_039192
  · exact g32p_supplierForest_actual_039213
  · exact g32p_supplierForest_actual_039218
  · exact g32p_supplierForest_actual_039220
  · exact g32p_supplierForest_actual_039299
  · exact g32p_supplierForest_actual_039313
  · exact g32p_supplierForest_actual_039338
  · exact g32p_supplierForest_actual_039356
  · exact g32p_supplierForest_actual_039395
  · exact g32p_supplierForest_actual_039561
  · exact g32p_supplierForest_actual_039564
  · exact g32p_supplierForest_actual_039591
  · exact g32p_supplierForest_actual_039630
  · exact g32p_supplierForest_actual_039663
  · exact g32p_supplierForest_actual_039686
  · exact g32p_supplierForest_actual_039713
  · exact g32p_supplierForest_actual_039719
  · exact g32p_supplierForest_actual_039727
  · exact g32p_supplierForest_actual_039730
  · exact g32p_supplierForest_actual_039756
  · exact g32p_supplierForest_actual_039806
  · exact g32p_supplierForest_actual_039811
  · exact g32p_supplierForest_actual_039814
  · exact g32p_supplierForest_actual_039829
  · exact g32p_supplierForest_actual_039845
  · exact g32p_supplierForest_actual_039855
  · exact g32p_supplierForest_actual_039869
  · exact g32p_supplierForest_actual_039872
  · exact g32p_supplierForest_actual_039915
  · exact g32p_supplierForest_actual_039929
  · exact g32p_supplierForest_actual_039950
  · exact g32p_supplierForest_actual_040011
  · exact g32p_supplierForest_actual_040027
  · exact g32p_supplierForest_actual_040038
  · exact g32p_supplierForest_actual_040057
  · exact g32p_supplierForest_actual_040073
  · exact g32p_supplierForest_actual_040075
  · exact g32p_supplierForest_actual_040076
  · exact g32p_supplierForest_actual_040082
  · exact g32p_supplierForest_actual_040103
  · exact g32p_supplierForest_actual_040104
  · exact g32p_supplierForest_actual_040218
  · exact g32p_supplierForest_actual_040303
  · exact g32p_supplierForest_actual_040306
  · exact g32p_supplierForest_actual_040328
  · exact g32p_supplierForest_actual_040372
  · exact g32p_supplierForest_actual_040404
  · exact g32p_supplierForest_actual_040444
  · exact g32p_supplierForest_actual_040457
  · exact g32p_supplierForest_actual_040523
  · exact g32p_supplierForest_actual_040568
  · exact g32p_supplierForest_actual_040618
  · exact g32p_supplierForest_actual_040740
  · exact g32p_supplierForest_actual_040762
  · exact g32p_supplierForest_actual_040773
  · exact g32p_supplierForest_actual_040774
  · exact g32p_supplierForest_actual_040779
  · exact g32p_supplierForest_actual_040884
  · exact g32p_supplierForest_actual_040916
  · exact g32p_supplierForest_actual_040937
  · exact g32p_supplierForest_actual_040954
  · exact g32p_supplierForest_actual_040987
  · exact g32p_supplierForest_actual_041008
  · exact g32p_supplierForest_actual_041058
  · exact g32p_supplierForest_actual_041131
  · exact g32p_supplierForest_actual_041138
  · exact g32p_supplierForest_actual_041158
  · exact g32p_supplierForest_actual_041163
  · exact g32p_supplierForest_actual_041203
  · exact g32p_supplierForest_actual_041225
  · exact g32p_supplierForest_actual_041365
  · exact g32p_supplierForest_actual_041396
  · exact g32p_supplierForest_actual_041442
  · exact g32p_supplierForest_actual_041526
  · exact g32p_supplierForest_actual_041532
  · exact g32p_supplierForest_actual_041538
  · exact g32p_supplierForest_actual_041557
  · exact g32p_supplierForest_actual_041560
  · exact g32p_supplierForest_actual_041564
  · exact g32p_supplierForest_actual_041568
  · exact g32p_supplierForest_actual_041594
  · exact g32p_supplierForest_actual_041600
  · exact g32p_supplierForest_actual_041695
  · exact g32p_supplierForest_actual_041728
  · exact g32p_supplierForest_actual_041735
  · exact g32p_supplierForest_actual_041774
  · exact g32p_supplierForest_actual_041811
  · exact g32p_supplierForest_actual_041819
  · exact g32p_supplierForest_actual_041842
  · exact g32p_supplierForest_actual_041855
  · exact g32p_supplierForest_actual_041871
  · exact g32p_supplierForest_actual_041941
  · exact g32p_supplierForest_actual_041972
  · exact g32p_supplierForest_actual_041986
  · exact g32p_supplierForest_actual_042009
  · exact g32p_supplierForest_actual_042010
  · exact g32p_supplierForest_actual_042139
  · exact g32p_supplierForest_actual_042147
  · exact g32p_supplierForest_actual_042148
  · exact g32p_supplierForest_actual_042225
  · exact g32p_supplierForest_actual_042229
  · exact g32p_supplierForest_actual_042262
  · exact g32p_supplierForest_actual_042290
  · exact g32p_supplierForest_actual_042313
  · exact g32p_supplierForest_actual_042378
  · exact g32p_supplierForest_actual_042394
  · exact g32p_supplierForest_actual_042427
  · exact g32p_supplierForest_actual_042488
  · exact g32p_supplierForest_actual_042561
  · exact g32p_supplierForest_actual_042563
  · exact g32p_supplierForest_actual_042577
  · exact g32p_supplierForest_actual_042629
  · exact g32p_supplierForest_actual_042633
  · exact g32p_supplierForest_actual_042662
  · exact g32p_supplierForest_actual_042663
  · exact g32p_supplierForest_actual_042673
  · exact g32p_supplierForest_actual_042727
  · exact g32p_supplierForest_actual_042770
  · exact g32p_supplierForest_actual_042777
  · exact g32p_supplierForest_actual_042825
  · exact g32p_supplierForest_actual_042853
  · exact g32p_supplierForest_actual_042931
  · exact g32p_supplierForest_actual_042994
  · exact g32p_supplierForest_actual_043041
  · exact g32p_supplierForest_actual_043043
  · exact g32p_supplierForest_actual_043086
  · exact g32p_supplierForest_actual_043148
  · exact g32p_supplierForest_actual_043178
  · exact g32p_supplierForest_actual_043180
  · exact g32p_supplierForest_actual_043196
  · exact g32p_supplierForest_actual_043203
  · exact g32p_supplierForest_actual_043209
  · exact g32p_supplierForest_actual_043212
  · exact g32p_supplierForest_actual_043282
  · exact g32p_supplierForest_actual_043347
  · exact g32p_supplierForest_actual_043349
  · exact g32p_supplierForest_actual_043364
  · exact g32p_supplierForest_actual_043373
  · exact g32p_supplierForest_actual_043374
  · exact g32p_supplierForest_actual_043408
  · exact g32p_supplierForest_actual_043510
  · exact g32p_supplierForest_actual_043520
  · exact g32p_supplierForest_actual_043572
  · exact g32p_supplierForest_actual_043605
  · exact g32p_supplierForest_actual_043619
  · exact g32p_supplierForest_actual_043657
  · exact g32p_supplierForest_actual_043711
  · exact g32p_supplierForest_actual_043762
  · exact g32p_supplierForest_actual_043779
  · exact g32p_supplierForest_actual_043817
  · exact g32p_supplierForest_actual_043828
  · exact g32p_supplierForest_actual_043834
  · exact g32p_supplierForest_actual_043888
  · exact g32p_supplierForest_actual_043934
  · exact g32p_supplierForest_actual_043942
  · exact g32p_supplierForest_actual_043950

def g32p_supplierForest_nodes_117 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_043958 else g32p_supplierForest_node_043977) else (if i.val < 3 then g32p_supplierForest_node_044019 else g32p_supplierForest_node_044062)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_044065 else g32p_supplierForest_node_044085) else (if i.val < 7 then g32p_supplierForest_node_044114 else g32p_supplierForest_node_044168))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_044180 else g32p_supplierForest_node_044237) else (if i.val < 11 then g32p_supplierForest_node_044271 else g32p_supplierForest_node_044291)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_044318 else g32p_supplierForest_node_044332) else (if i.val < 15 then g32p_supplierForest_node_044369 else g32p_supplierForest_node_044444)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_044447 else g32p_supplierForest_node_044455) else (if i.val < 19 then g32p_supplierForest_node_044457 else g32p_supplierForest_node_044563)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_044614 else g32p_supplierForest_node_044617) else (if i.val < 23 then g32p_supplierForest_node_044621 else g32p_supplierForest_node_044681))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_044699 else g32p_supplierForest_node_044745) else (if i.val < 27 then g32p_supplierForest_node_044794 else g32p_supplierForest_node_044816)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_044954 else g32p_supplierForest_node_045015) else (if i.val < 31 then g32p_supplierForest_node_045048 else g32p_supplierForest_node_045056))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_045059 else g32p_supplierForest_node_045107) else (if i.val < 35 then g32p_supplierForest_node_045128 else g32p_supplierForest_node_045209)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_045303 else g32p_supplierForest_node_045338) else (if i.val < 39 then g32p_supplierForest_node_045358 else g32p_supplierForest_node_045484))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_045509 else g32p_supplierForest_node_045515) else (if i.val < 43 then g32p_supplierForest_node_045516 else g32p_supplierForest_node_045539)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_045587 else g32p_supplierForest_node_045638) else (if i.val < 47 then g32p_supplierForest_node_045677 else g32p_supplierForest_node_045701)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_045722 else g32p_supplierForest_node_045727) else (if i.val < 51 then g32p_supplierForest_node_045735 else g32p_supplierForest_node_045737)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_045747 else g32p_supplierForest_node_045749) else (if i.val < 55 then g32p_supplierForest_node_045757 else g32p_supplierForest_node_045802))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_045840 else g32p_supplierForest_node_045875) else (if i.val < 59 then g32p_supplierForest_node_045881 else g32p_supplierForest_node_045884)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_045899 else g32p_supplierForest_node_045940) else (if i.val < 63 then g32p_supplierForest_node_045989 else g32p_supplierForest_node_046006)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_046041 else g32p_supplierForest_node_046070) else (if i.val < 67 then g32p_supplierForest_node_046102 else g32p_supplierForest_node_046111)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_046119 else g32p_supplierForest_node_046178) else (if i.val < 71 then g32p_supplierForest_node_046179 else g32p_supplierForest_node_046181))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_046242 else g32p_supplierForest_node_046303) else (if i.val < 75 then g32p_supplierForest_node_046336 else g32p_supplierForest_node_046352)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_046356 else g32p_supplierForest_node_046383) else (if i.val < 79 then g32p_supplierForest_node_046392 else g32p_supplierForest_node_046414)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_046417 else g32p_supplierForest_node_046430) else (if i.val < 83 then g32p_supplierForest_node_046489 else g32p_supplierForest_node_046494)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_046502 else g32p_supplierForest_node_046516) else (if i.val < 87 then g32p_supplierForest_node_046552 else g32p_supplierForest_node_046556))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_046558 else g32p_supplierForest_node_046608) else (if i.val < 91 then g32p_supplierForest_node_046621 else g32p_supplierForest_node_046633)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_046653 else g32p_supplierForest_node_046679) else (if i.val < 95 then g32p_supplierForest_node_046767 else g32p_supplierForest_node_046769))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_046780 else g32p_supplierForest_node_046783) else (if i.val < 99 then g32p_supplierForest_node_046803 else g32p_supplierForest_node_046816)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_046817 else g32p_supplierForest_node_046839) else (if i.val < 103 then g32p_supplierForest_node_046856 else g32p_supplierForest_node_046880))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_046900 else g32p_supplierForest_node_046923) else (if i.val < 107 then g32p_supplierForest_node_046927 else g32p_supplierForest_node_046930)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_046953 else g32p_supplierForest_node_046972) else (if i.val < 111 then g32p_supplierForest_node_046981 else g32p_supplierForest_node_047083)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_047122 else g32p_supplierForest_node_047135) else (if i.val < 115 then g32p_supplierForest_node_047137 else g32p_supplierForest_node_047141)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_047214 else g32p_supplierForest_node_047319) else (if i.val < 119 then g32p_supplierForest_node_047351 else g32p_supplierForest_node_047359))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_047418 else g32p_supplierForest_node_047423) else (if i.val < 123 then g32p_supplierForest_node_047457 else g32p_supplierForest_node_047477)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_047564 else g32p_supplierForest_node_047567) else (if i.val < 127 then g32p_supplierForest_node_047579 else g32p_supplierForest_node_047680))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_047747 else g32p_supplierForest_node_047793) else (if i.val < 131 then g32p_supplierForest_node_047806 else g32p_supplierForest_node_047833)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_047842 else g32p_supplierForest_node_047846) else (if i.val < 135 then g32p_supplierForest_node_047892 else g32p_supplierForest_node_047898))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_047899 else g32p_supplierForest_node_047937) else (if i.val < 139 then g32p_supplierForest_node_048041 else g32p_supplierForest_node_048060)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_048080 else g32p_supplierForest_node_048103) else (if i.val < 143 then g32p_supplierForest_node_048108 else g32p_supplierForest_node_048155)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_048227 else g32p_supplierForest_node_048306) else (if i.val < 147 then g32p_supplierForest_node_048362 else g32p_supplierForest_node_048488)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_048517 else g32p_supplierForest_node_048634) else (if i.val < 151 then g32p_supplierForest_node_048649 else g32p_supplierForest_node_048677))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_048777 else g32p_supplierForest_node_048784) else (if i.val < 155 then g32p_supplierForest_node_048804 else g32p_supplierForest_node_048866)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_048901 else g32p_supplierForest_node_048949) else (if i.val < 159 then g32p_supplierForest_node_048958 else g32p_supplierForest_node_048979))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_049008 else g32p_supplierForest_node_049010) else (if i.val < 163 then g32p_supplierForest_node_049026 else g32p_supplierForest_node_049044)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_049056 else g32p_supplierForest_node_049072) else (if i.val < 167 then g32p_supplierForest_node_049125 else g32p_supplierForest_node_049149))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_049201 else g32p_supplierForest_node_049210) else (if i.val < 171 then g32p_supplierForest_node_049222 else g32p_supplierForest_node_049233)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_049341 else g32p_supplierForest_node_049342) else (if i.val < 175 then g32p_supplierForest_node_049366 else g32p_supplierForest_node_049408)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_049445 else g32p_supplierForest_node_049448) else (if i.val < 179 then g32p_supplierForest_node_049452 else g32p_supplierForest_node_049475)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_049485 else g32p_supplierForest_node_049516) else (if i.val < 183 then g32p_supplierForest_node_049560 else g32p_supplierForest_node_049568))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_049610 else g32p_supplierForest_node_049633) else (if i.val < 187 then g32p_supplierForest_node_049694 else g32p_supplierForest_node_049697)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_049718 else g32p_supplierForest_node_049735) else (if i.val < 191 then g32p_supplierForest_node_049788 else g32p_supplierForest_node_049813)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_049820 else g32p_supplierForest_node_049855) else (if i.val < 195 then g32p_supplierForest_node_049868 else g32p_supplierForest_node_049873)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_049886 else g32p_supplierForest_node_049901) else (if i.val < 199 then g32p_supplierForest_node_049940 else g32p_supplierForest_node_049996))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_050064 else g32p_supplierForest_node_050097) else (if i.val < 203 then g32p_supplierForest_node_050116 else g32p_supplierForest_node_050124)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_050145 else g32p_supplierForest_node_050147) else (if i.val < 207 then g32p_supplierForest_node_050152 else g32p_supplierForest_node_050174)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_050192 else g32p_supplierForest_node_050195) else (if i.val < 211 then g32p_supplierForest_node_050221 else g32p_supplierForest_node_050241)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_050268 else g32p_supplierForest_node_050280) else (if i.val < 215 then g32p_supplierForest_node_050290 else g32p_supplierForest_node_050294))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_050316 else g32p_supplierForest_node_050364) else (if i.val < 219 then g32p_supplierForest_node_050402 else g32p_supplierForest_node_050441)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_050458 else g32p_supplierForest_node_050485) else (if i.val < 223 then g32p_supplierForest_node_050498 else g32p_supplierForest_node_050510))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_050550 else g32p_supplierForest_node_050595) else (if i.val < 227 then g32p_supplierForest_node_050653 else g32p_supplierForest_node_050664)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_050668 else g32p_supplierForest_node_050677) else (if i.val < 231 then g32p_supplierForest_node_050725 else g32p_supplierForest_node_050754))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_050763 else g32p_supplierForest_node_050783) else (if i.val < 235 then g32p_supplierForest_node_050807 else g32p_supplierForest_node_050810)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_050831 else g32p_supplierForest_node_050836) else (if i.val < 239 then g32p_supplierForest_node_050848 else g32p_supplierForest_node_050902)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_050917 else g32p_supplierForest_node_050949) else (if i.val < 243 then g32p_supplierForest_node_050969 else g32p_supplierForest_node_050984)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_051002 else g32p_supplierForest_node_051007) else (if i.val < 247 then g32p_supplierForest_node_051040 else g32p_supplierForest_node_051042))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_051117 else g32p_supplierForest_node_051254) else (if i.val < 251 then g32p_supplierForest_node_051264 else g32p_supplierForest_node_051314)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_051324 else g32p_supplierForest_node_051378) else (if i.val < 255 then g32p_supplierForest_node_051443 else g32p_supplierForest_node_051479))))))))

def g32p_supplierForest_classes_117 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 29) else (if i.val < 3 then 57 else 15)) else (if i.val < 6 then (if i.val < 5 then 60 else 14) else (if i.val < 7 then 14 else 60))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 29 else 30) else (if i.val < 11 then 15 else 63)) else (if i.val < 14 then (if i.val < 13 then 58 else 57) else (if i.val < 15 then 57 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 41 else 38) else (if i.val < 19 then 21 else 39)) else (if i.val < 22 then (if i.val < 21 then 40 else 22) else (if i.val < 23 then 38 else 21))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 38 else 39) else (if i.val < 27 then 21 else 21)) else (if i.val < 30 then (if i.val < 29 then 38 else 43) else (if i.val < 31 then 70 else 21))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 22 else 21) else (if i.val < 35 then 21 else 38)) else (if i.val < 38 then (if i.val < 37 then 21 else 68) else (if i.val < 39 then 22 else 21))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 74 else 40) else (if i.val < 43 then 21 else 38)) else (if i.val < 46 then (if i.val < 45 then 22 else 22) else (if i.val < 47 then 38 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 38 else 21) else (if i.val < 51 then 38 else 22)) else (if i.val < 54 then (if i.val < 53 then 38 else 38) else (if i.val < 55 then 21 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 74) else (if i.val < 59 then 71 else 38)) else (if i.val < 62 then (if i.val < 61 then 38 else 7) else (if i.val < 63 then 74 else 38)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 38 else 20) else (if i.val < 67 then 71 else 38)) else (if i.val < 70 then (if i.val < 69 then 40 else 38) else (if i.val < 71 then 22 else 39))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 21 else 68) else (if i.val < 75 then 70 else 21)) else (if i.val < 78 then (if i.val < 77 then 38 else 7) else (if i.val < 79 then 38 else 73)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 21 else 22) else (if i.val < 83 then 38 else 43)) else (if i.val < 86 then (if i.val < 85 then 38 else 74) else (if i.val < 87 then 38 else 22))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 72 else 22) else (if i.val < 91 then 21 else 38)) else (if i.val < 94 then (if i.val < 93 then 38 else 38) else (if i.val < 95 then 21 else 21))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 19 else 21) else (if i.val < 99 then 41 else 21)) else (if i.val < 102 then (if i.val < 101 then 22 else 38) else (if i.val < 103 then 40 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 19 else 75) else (if i.val < 107 then 40 else 74)) else (if i.val < 110 then (if i.val < 109 then 21 else 38) else (if i.val < 111 then 74 else 70)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 40 else 38) else (if i.val < 115 then 38 else 38)) else (if i.val < 118 then (if i.val < 117 then 21 else 40) else (if i.val < 119 then 38 else 7))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 43 else 38) else (if i.val < 123 then 38 else 21)) else (if i.val < 126 then (if i.val < 125 then 38 else 40) else (if i.val < 127 then 21 else 40))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 75 else 73) else (if i.val < 131 then 73 else 74)) else (if i.val < 134 then (if i.val < 133 then 22 else 40) else (if i.val < 135 then 43 else 38))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 20 else 38) else (if i.val < 139 then 22 else 19)) else (if i.val < 142 then (if i.val < 141 then 7 else 39) else (if i.val < 143 then 43 else 40)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 21 else 22) else (if i.val < 147 then 21 else 74)) else (if i.val < 150 then (if i.val < 149 then 43 else 73) else (if i.val < 151 then 22 else 74))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 74 else 70) else (if i.val < 155 then 70 else 21)) else (if i.val < 158 then (if i.val < 157 then 38 else 21) else (if i.val < 159 then 38 else 22))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 38 else 21) else (if i.val < 163 then 21 else 68)) else (if i.val < 166 then (if i.val < 165 then 21 else 70) else (if i.val < 167 then 68 else 21))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 21) else (if i.val < 171 then 42 else 70)) else (if i.val < 174 then (if i.val < 173 then 38 else 38) else (if i.val < 175 then 43 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 22) else (if i.val < 179 then 70 else 38)) else (if i.val < 182 then (if i.val < 181 then 21 else 21) else (if i.val < 183 then 38 else 22))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 22 else 38) else (if i.val < 187 then 21 else 38)) else (if i.val < 190 then (if i.val < 189 then 22 else 22) else (if i.val < 191 then 71 else 21)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 72 else 22) else (if i.val < 195 then 22 else 38)) else (if i.val < 198 then (if i.val < 197 then 23 else 22) else (if i.val < 199 then 6 else 21))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 22 else 38) else (if i.val < 203 then 21 else 38)) else (if i.val < 206 then (if i.val < 205 then 7 else 38) else (if i.val < 207 then 21 else 21)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 40 else 22) else (if i.val < 211 then 39 else 20)) else (if i.val < 214 then (if i.val < 213 then 21 else 21) else (if i.val < 215 then 38 else 21))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 39 else 40) else (if i.val < 219 then 22 else 21)) else (if i.val < 222 then (if i.val < 221 then 38 else 39) else (if i.val < 223 then 41 else 73))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 38 else 38) else (if i.val < 227 then 21 else 71)) else (if i.val < 230 then (if i.val < 229 then 7 else 22) else (if i.val < 231 then 23 else 71))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 22 else 20) else (if i.val < 235 then 22 else 40)) else (if i.val < 238 then (if i.val < 237 then 21 else 21) else (if i.val < 239 then 21 else 5)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 71 else 21) else (if i.val < 243 then 21 else 38)) else (if i.val < 246 then (if i.val < 245 then 21 else 22) else (if i.val < 247 then 38 else 22))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 21 else 39) else (if i.val < 251 then 21 else 38)) else (if i.val < 254 then (if i.val < 253 then 22 else 21) else (if i.val < 255 then 38 else 38))))))))

theorem g32p_supplierForest_actual_117 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_117 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_117 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_043958
  · exact g32p_supplierForest_actual_043977
  · exact g32p_supplierForest_actual_044019
  · exact g32p_supplierForest_actual_044062
  · exact g32p_supplierForest_actual_044065
  · exact g32p_supplierForest_actual_044085
  · exact g32p_supplierForest_actual_044114
  · exact g32p_supplierForest_actual_044168
  · exact g32p_supplierForest_actual_044180
  · exact g32p_supplierForest_actual_044237
  · exact g32p_supplierForest_actual_044271
  · exact g32p_supplierForest_actual_044291
  · exact g32p_supplierForest_actual_044318
  · exact g32p_supplierForest_actual_044332
  · exact g32p_supplierForest_actual_044369
  · exact g32p_supplierForest_actual_044444
  · exact g32p_supplierForest_actual_044447
  · exact g32p_supplierForest_actual_044455
  · exact g32p_supplierForest_actual_044457
  · exact g32p_supplierForest_actual_044563
  · exact g32p_supplierForest_actual_044614
  · exact g32p_supplierForest_actual_044617
  · exact g32p_supplierForest_actual_044621
  · exact g32p_supplierForest_actual_044681
  · exact g32p_supplierForest_actual_044699
  · exact g32p_supplierForest_actual_044745
  · exact g32p_supplierForest_actual_044794
  · exact g32p_supplierForest_actual_044816
  · exact g32p_supplierForest_actual_044954
  · exact g32p_supplierForest_actual_045015
  · exact g32p_supplierForest_actual_045048
  · exact g32p_supplierForest_actual_045056
  · exact g32p_supplierForest_actual_045059
  · exact g32p_supplierForest_actual_045107
  · exact g32p_supplierForest_actual_045128
  · exact g32p_supplierForest_actual_045209
  · exact g32p_supplierForest_actual_045303
  · exact g32p_supplierForest_actual_045338
  · exact g32p_supplierForest_actual_045358
  · exact g32p_supplierForest_actual_045484
  · exact g32p_supplierForest_actual_045509
  · exact g32p_supplierForest_actual_045515
  · exact g32p_supplierForest_actual_045516
  · exact g32p_supplierForest_actual_045539
  · exact g32p_supplierForest_actual_045587
  · exact g32p_supplierForest_actual_045638
  · exact g32p_supplierForest_actual_045677
  · exact g32p_supplierForest_actual_045701
  · exact g32p_supplierForest_actual_045722
  · exact g32p_supplierForest_actual_045727
  · exact g32p_supplierForest_actual_045735
  · exact g32p_supplierForest_actual_045737
  · exact g32p_supplierForest_actual_045747
  · exact g32p_supplierForest_actual_045749
  · exact g32p_supplierForest_actual_045757
  · exact g32p_supplierForest_actual_045802
  · exact g32p_supplierForest_actual_045840
  · exact g32p_supplierForest_actual_045875
  · exact g32p_supplierForest_actual_045881
  · exact g32p_supplierForest_actual_045884
  · exact g32p_supplierForest_actual_045899
  · exact g32p_supplierForest_actual_045940
  · exact g32p_supplierForest_actual_045989
  · exact g32p_supplierForest_actual_046006
  · exact g32p_supplierForest_actual_046041
  · exact g32p_supplierForest_actual_046070
  · exact g32p_supplierForest_actual_046102
  · exact g32p_supplierForest_actual_046111
  · exact g32p_supplierForest_actual_046119
  · exact g32p_supplierForest_actual_046178
  · exact g32p_supplierForest_actual_046179
  · exact g32p_supplierForest_actual_046181
  · exact g32p_supplierForest_actual_046242
  · exact g32p_supplierForest_actual_046303
  · exact g32p_supplierForest_actual_046336
  · exact g32p_supplierForest_actual_046352
  · exact g32p_supplierForest_actual_046356
  · exact g32p_supplierForest_actual_046383
  · exact g32p_supplierForest_actual_046392
  · exact g32p_supplierForest_actual_046414
  · exact g32p_supplierForest_actual_046417
  · exact g32p_supplierForest_actual_046430
  · exact g32p_supplierForest_actual_046489
  · exact g32p_supplierForest_actual_046494
  · exact g32p_supplierForest_actual_046502
  · exact g32p_supplierForest_actual_046516
  · exact g32p_supplierForest_actual_046552
  · exact g32p_supplierForest_actual_046556
  · exact g32p_supplierForest_actual_046558
  · exact g32p_supplierForest_actual_046608
  · exact g32p_supplierForest_actual_046621
  · exact g32p_supplierForest_actual_046633
  · exact g32p_supplierForest_actual_046653
  · exact g32p_supplierForest_actual_046679
  · exact g32p_supplierForest_actual_046767
  · exact g32p_supplierForest_actual_046769
  · exact g32p_supplierForest_actual_046780
  · exact g32p_supplierForest_actual_046783
  · exact g32p_supplierForest_actual_046803
  · exact g32p_supplierForest_actual_046816
  · exact g32p_supplierForest_actual_046817
  · exact g32p_supplierForest_actual_046839
  · exact g32p_supplierForest_actual_046856
  · exact g32p_supplierForest_actual_046880
  · exact g32p_supplierForest_actual_046900
  · exact g32p_supplierForest_actual_046923
  · exact g32p_supplierForest_actual_046927
  · exact g32p_supplierForest_actual_046930
  · exact g32p_supplierForest_actual_046953
  · exact g32p_supplierForest_actual_046972
  · exact g32p_supplierForest_actual_046981
  · exact g32p_supplierForest_actual_047083
  · exact g32p_supplierForest_actual_047122
  · exact g32p_supplierForest_actual_047135
  · exact g32p_supplierForest_actual_047137
  · exact g32p_supplierForest_actual_047141
  · exact g32p_supplierForest_actual_047214
  · exact g32p_supplierForest_actual_047319
  · exact g32p_supplierForest_actual_047351
  · exact g32p_supplierForest_actual_047359
  · exact g32p_supplierForest_actual_047418
  · exact g32p_supplierForest_actual_047423
  · exact g32p_supplierForest_actual_047457
  · exact g32p_supplierForest_actual_047477
  · exact g32p_supplierForest_actual_047564
  · exact g32p_supplierForest_actual_047567
  · exact g32p_supplierForest_actual_047579
  · exact g32p_supplierForest_actual_047680
  · exact g32p_supplierForest_actual_047747
  · exact g32p_supplierForest_actual_047793
  · exact g32p_supplierForest_actual_047806
  · exact g32p_supplierForest_actual_047833
  · exact g32p_supplierForest_actual_047842
  · exact g32p_supplierForest_actual_047846
  · exact g32p_supplierForest_actual_047892
  · exact g32p_supplierForest_actual_047898
  · exact g32p_supplierForest_actual_047899
  · exact g32p_supplierForest_actual_047937
  · exact g32p_supplierForest_actual_048041
  · exact g32p_supplierForest_actual_048060
  · exact g32p_supplierForest_actual_048080
  · exact g32p_supplierForest_actual_048103
  · exact g32p_supplierForest_actual_048108
  · exact g32p_supplierForest_actual_048155
  · exact g32p_supplierForest_actual_048227
  · exact g32p_supplierForest_actual_048306
  · exact g32p_supplierForest_actual_048362
  · exact g32p_supplierForest_actual_048488
  · exact g32p_supplierForest_actual_048517
  · exact g32p_supplierForest_actual_048634
  · exact g32p_supplierForest_actual_048649
  · exact g32p_supplierForest_actual_048677
  · exact g32p_supplierForest_actual_048777
  · exact g32p_supplierForest_actual_048784
  · exact g32p_supplierForest_actual_048804
  · exact g32p_supplierForest_actual_048866
  · exact g32p_supplierForest_actual_048901
  · exact g32p_supplierForest_actual_048949
  · exact g32p_supplierForest_actual_048958
  · exact g32p_supplierForest_actual_048979
  · exact g32p_supplierForest_actual_049008
  · exact g32p_supplierForest_actual_049010
  · exact g32p_supplierForest_actual_049026
  · exact g32p_supplierForest_actual_049044
  · exact g32p_supplierForest_actual_049056
  · exact g32p_supplierForest_actual_049072
  · exact g32p_supplierForest_actual_049125
  · exact g32p_supplierForest_actual_049149
  · exact g32p_supplierForest_actual_049201
  · exact g32p_supplierForest_actual_049210
  · exact g32p_supplierForest_actual_049222
  · exact g32p_supplierForest_actual_049233
  · exact g32p_supplierForest_actual_049341
  · exact g32p_supplierForest_actual_049342
  · exact g32p_supplierForest_actual_049366
  · exact g32p_supplierForest_actual_049408
  · exact g32p_supplierForest_actual_049445
  · exact g32p_supplierForest_actual_049448
  · exact g32p_supplierForest_actual_049452
  · exact g32p_supplierForest_actual_049475
  · exact g32p_supplierForest_actual_049485
  · exact g32p_supplierForest_actual_049516
  · exact g32p_supplierForest_actual_049560
  · exact g32p_supplierForest_actual_049568
  · exact g32p_supplierForest_actual_049610
  · exact g32p_supplierForest_actual_049633
  · exact g32p_supplierForest_actual_049694
  · exact g32p_supplierForest_actual_049697
  · exact g32p_supplierForest_actual_049718
  · exact g32p_supplierForest_actual_049735
  · exact g32p_supplierForest_actual_049788
  · exact g32p_supplierForest_actual_049813
  · exact g32p_supplierForest_actual_049820
  · exact g32p_supplierForest_actual_049855
  · exact g32p_supplierForest_actual_049868
  · exact g32p_supplierForest_actual_049873
  · exact g32p_supplierForest_actual_049886
  · exact g32p_supplierForest_actual_049901
  · exact g32p_supplierForest_actual_049940
  · exact g32p_supplierForest_actual_049996
  · exact g32p_supplierForest_actual_050064
  · exact g32p_supplierForest_actual_050097
  · exact g32p_supplierForest_actual_050116
  · exact g32p_supplierForest_actual_050124
  · exact g32p_supplierForest_actual_050145
  · exact g32p_supplierForest_actual_050147
  · exact g32p_supplierForest_actual_050152
  · exact g32p_supplierForest_actual_050174
  · exact g32p_supplierForest_actual_050192
  · exact g32p_supplierForest_actual_050195
  · exact g32p_supplierForest_actual_050221
  · exact g32p_supplierForest_actual_050241
  · exact g32p_supplierForest_actual_050268
  · exact g32p_supplierForest_actual_050280
  · exact g32p_supplierForest_actual_050290
  · exact g32p_supplierForest_actual_050294
  · exact g32p_supplierForest_actual_050316
  · exact g32p_supplierForest_actual_050364
  · exact g32p_supplierForest_actual_050402
  · exact g32p_supplierForest_actual_050441
  · exact g32p_supplierForest_actual_050458
  · exact g32p_supplierForest_actual_050485
  · exact g32p_supplierForest_actual_050498
  · exact g32p_supplierForest_actual_050510
  · exact g32p_supplierForest_actual_050550
  · exact g32p_supplierForest_actual_050595
  · exact g32p_supplierForest_actual_050653
  · exact g32p_supplierForest_actual_050664
  · exact g32p_supplierForest_actual_050668
  · exact g32p_supplierForest_actual_050677
  · exact g32p_supplierForest_actual_050725
  · exact g32p_supplierForest_actual_050754
  · exact g32p_supplierForest_actual_050763
  · exact g32p_supplierForest_actual_050783
  · exact g32p_supplierForest_actual_050807
  · exact g32p_supplierForest_actual_050810
  · exact g32p_supplierForest_actual_050831
  · exact g32p_supplierForest_actual_050836
  · exact g32p_supplierForest_actual_050848
  · exact g32p_supplierForest_actual_050902
  · exact g32p_supplierForest_actual_050917
  · exact g32p_supplierForest_actual_050949
  · exact g32p_supplierForest_actual_050969
  · exact g32p_supplierForest_actual_050984
  · exact g32p_supplierForest_actual_051002
  · exact g32p_supplierForest_actual_051007
  · exact g32p_supplierForest_actual_051040
  · exact g32p_supplierForest_actual_051042
  · exact g32p_supplierForest_actual_051117
  · exact g32p_supplierForest_actual_051254
  · exact g32p_supplierForest_actual_051264
  · exact g32p_supplierForest_actual_051314
  · exact g32p_supplierForest_actual_051324
  · exact g32p_supplierForest_actual_051378
  · exact g32p_supplierForest_actual_051443
  · exact g32p_supplierForest_actual_051479

def g32p_supplierForest_nodes_118 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_051491 else g32p_supplierForest_node_051493) else (if i.val < 3 then g32p_supplierForest_node_051496 else g32p_supplierForest_node_051504)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_051528 else g32p_supplierForest_node_051544) else (if i.val < 7 then g32p_supplierForest_node_051581 else g32p_supplierForest_node_051613))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_051619 else g32p_supplierForest_node_051675) else (if i.val < 11 then g32p_supplierForest_node_051684 else g32p_supplierForest_node_051767)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_051874 else g32p_supplierForest_node_051936) else (if i.val < 15 then g32p_supplierForest_node_051962 else g32p_supplierForest_node_052058)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_052059 else g32p_supplierForest_node_052062) else (if i.val < 19 then g32p_supplierForest_node_052086 else g32p_supplierForest_node_052089)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_052092 else g32p_supplierForest_node_052104) else (if i.val < 23 then g32p_supplierForest_node_052114 else g32p_supplierForest_node_052131))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_052143 else g32p_supplierForest_node_052147) else (if i.val < 27 then g32p_supplierForest_node_052227 else g32p_supplierForest_node_052256)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_052284 else g32p_supplierForest_node_052303) else (if i.val < 31 then g32p_supplierForest_node_052365 else g32p_supplierForest_node_052394))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_052481 else g32p_supplierForest_node_052598) else (if i.val < 35 then g32p_supplierForest_node_052661 else g32p_supplierForest_node_052665)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_052707 else g32p_supplierForest_node_052719) else (if i.val < 39 then g32p_supplierForest_node_052740 else g32p_supplierForest_node_052802))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_052811 else g32p_supplierForest_node_052813) else (if i.val < 43 then g32p_supplierForest_node_052864 else g32p_supplierForest_node_052940)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_052949 else g32p_supplierForest_node_053026) else (if i.val < 47 then g32p_supplierForest_node_053031 else g32p_supplierForest_node_053170)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_053172 else g32p_supplierForest_node_053188) else (if i.val < 51 then g32p_supplierForest_node_053297 else g32p_supplierForest_node_053313)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_053325 else g32p_supplierForest_node_053372) else (if i.val < 55 then g32p_supplierForest_node_053415 else g32p_supplierForest_node_053454))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_053461 else g32p_supplierForest_node_053489) else (if i.val < 59 then g32p_supplierForest_node_053514 else g32p_supplierForest_node_053533)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_053538 else g32p_supplierForest_node_053580) else (if i.val < 63 then g32p_supplierForest_node_053584 else g32p_supplierForest_node_053604)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_053616 else g32p_supplierForest_node_053619) else (if i.val < 67 then g32p_supplierForest_node_053637 else g32p_supplierForest_node_053647)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_053655 else g32p_supplierForest_node_053673) else (if i.val < 71 then g32p_supplierForest_node_053685 else g32p_supplierForest_node_053717))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_053733 else g32p_supplierForest_node_053786) else (if i.val < 75 then g32p_supplierForest_node_053806 else g32p_supplierForest_node_053921)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_054000 else g32p_supplierForest_node_054043) else (if i.val < 79 then g32p_supplierForest_node_054065 else g32p_supplierForest_node_054084)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_054085 else g32p_supplierForest_node_054107) else (if i.val < 83 then g32p_supplierForest_node_054110 else g32p_supplierForest_node_054159)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_054166 else g32p_supplierForest_node_054182) else (if i.val < 87 then g32p_supplierForest_node_054200 else g32p_supplierForest_node_054209))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_054269 else g32p_supplierForest_node_054275) else (if i.val < 91 then g32p_supplierForest_node_054370 else g32p_supplierForest_node_054381)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_054432 else g32p_supplierForest_node_054452) else (if i.val < 95 then g32p_supplierForest_node_054591 else g32p_supplierForest_node_054640))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_054653 else g32p_supplierForest_node_054658) else (if i.val < 99 then g32p_supplierForest_node_054707 else g32p_supplierForest_node_054722)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_054781 else g32p_supplierForest_node_054782) else (if i.val < 103 then g32p_supplierForest_node_054803 else g32p_supplierForest_node_054815))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_054832 else g32p_supplierForest_node_054834) else (if i.val < 107 then g32p_supplierForest_node_054901 else g32p_supplierForest_node_054977)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_054978 else g32p_supplierForest_node_054994) else (if i.val < 111 then g32p_supplierForest_node_055027 else g32p_supplierForest_node_055078)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_055118 else g32p_supplierForest_node_055123) else (if i.val < 115 then g32p_supplierForest_node_055130 else g32p_supplierForest_node_055151)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_055158 else g32p_supplierForest_node_055181) else (if i.val < 119 then g32p_supplierForest_node_055186 else g32p_supplierForest_node_055194))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_055201 else g32p_supplierForest_node_055213) else (if i.val < 123 then g32p_supplierForest_node_055230 else g32p_supplierForest_node_055278)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_055306 else g32p_supplierForest_node_055330) else (if i.val < 127 then g32p_supplierForest_node_055345 else g32p_supplierForest_node_055367))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_055416 else g32p_supplierForest_node_055420) else (if i.val < 131 then g32p_supplierForest_node_055424 else g32p_supplierForest_node_055465)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_055474 else g32p_supplierForest_node_055476) else (if i.val < 135 then g32p_supplierForest_node_055485 else g32p_supplierForest_node_055513))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_055587 else g32p_supplierForest_node_055596) else (if i.val < 139 then g32p_supplierForest_node_055660 else g32p_supplierForest_node_055663)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_055671 else g32p_supplierForest_node_055688) else (if i.val < 143 then g32p_supplierForest_node_055755 else g32p_supplierForest_node_055765)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_055772 else g32p_supplierForest_node_055774) else (if i.val < 147 then g32p_supplierForest_node_055781 else g32p_supplierForest_node_055814)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_055863 else g32p_supplierForest_node_055876) else (if i.val < 151 then g32p_supplierForest_node_055896 else g32p_supplierForest_node_055925))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_055980 else g32p_supplierForest_node_056033) else (if i.val < 155 then g32p_supplierForest_node_056111 else g32p_supplierForest_node_056131)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_056158 else g32p_supplierForest_node_056159) else (if i.val < 159 then g32p_supplierForest_node_056161 else g32p_supplierForest_node_056177))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_056184 else g32p_supplierForest_node_056202) else (if i.val < 163 then g32p_supplierForest_node_056229 else g32p_supplierForest_node_056290)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_056309 else g32p_supplierForest_node_056405) else (if i.val < 167 then g32p_supplierForest_node_056434 else g32p_supplierForest_node_056511))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_056547 else g32p_supplierForest_node_056559) else (if i.val < 171 then g32p_supplierForest_node_056599 else g32p_supplierForest_node_056738)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_056780 else g32p_supplierForest_node_056806) else (if i.val < 175 then g32p_supplierForest_node_056840 else g32p_supplierForest_node_056854)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_056935 else g32p_supplierForest_node_056938) else (if i.val < 179 then g32p_supplierForest_node_056993 else g32p_supplierForest_node_057022)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_057027 else g32p_supplierForest_node_057036) else (if i.val < 183 then g32p_supplierForest_node_057172 else g32p_supplierForest_node_057198))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_057242 else g32p_supplierForest_node_057287) else (if i.val < 187 then g32p_supplierForest_node_057323 else g32p_supplierForest_node_057361)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_057400 else g32p_supplierForest_node_057419) else (if i.val < 191 then g32p_supplierForest_node_057435 else g32p_supplierForest_node_057488)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_057512 else g32p_supplierForest_node_057513) else (if i.val < 195 then g32p_supplierForest_node_057519 else g32p_supplierForest_node_057522)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_057534 else g32p_supplierForest_node_057541) else (if i.val < 199 then g32p_supplierForest_node_057578 else g32p_supplierForest_node_057586))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_057605 else g32p_supplierForest_node_057615) else (if i.val < 203 then g32p_supplierForest_node_057633 else g32p_supplierForest_node_057672)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_057702 else g32p_supplierForest_node_057708) else (if i.val < 207 then g32p_supplierForest_node_057713 else g32p_supplierForest_node_057738)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_057741 else g32p_supplierForest_node_057775) else (if i.val < 211 then g32p_supplierForest_node_057780 else g32p_supplierForest_node_057799)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_057823 else g32p_supplierForest_node_057878) else (if i.val < 215 then g32p_supplierForest_node_057903 else g32p_supplierForest_node_057905))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_057947 else g32p_supplierForest_node_058026) else (if i.val < 219 then g32p_supplierForest_node_058067 else g32p_supplierForest_node_058093)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_058137 else g32p_supplierForest_node_058143) else (if i.val < 223 then g32p_supplierForest_node_058191 else g32p_supplierForest_node_058199))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_058242 else g32p_supplierForest_node_058285) else (if i.val < 227 then g32p_supplierForest_node_058309 else g32p_supplierForest_node_058318)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_058337 else g32p_supplierForest_node_058360) else (if i.val < 231 then g32p_supplierForest_node_058375 else g32p_supplierForest_node_058383))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_058501 else g32p_supplierForest_node_058532) else (if i.val < 235 then g32p_supplierForest_node_058539 else g32p_supplierForest_node_058562)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_058575 else g32p_supplierForest_node_058662) else (if i.val < 239 then g32p_supplierForest_node_058733 else g32p_supplierForest_node_058752)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_058753 else g32p_supplierForest_node_058832) else (if i.val < 243 then g32p_supplierForest_node_058861 else g32p_supplierForest_node_058864)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_058880 else g32p_supplierForest_node_058899) else (if i.val < 247 then g32p_supplierForest_node_058903 else g32p_supplierForest_node_058905))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_058934 else g32p_supplierForest_node_058958) else (if i.val < 251 then g32p_supplierForest_node_058963 else g32p_supplierForest_node_058992)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_059002 else g32p_supplierForest_node_059011) else (if i.val < 255 then g32p_supplierForest_node_059018 else g32p_supplierForest_node_059022))))))))

def g32p_supplierForest_classes_118 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 68 else 41) else (if i.val < 3 then 21 else 21)) else (if i.val < 6 then (if i.val < 5 then 41 else 22) else (if i.val < 7 then 38 else 40))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 41 else 21) else (if i.val < 11 then 38 else 38)) else (if i.val < 14 then (if i.val < 13 then 74 else 73) else (if i.val < 15 then 38 else 43)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 38 else 43) else (if i.val < 19 then 38 else 7)) else (if i.val < 22 then (if i.val < 21 then 38 else 38) else (if i.val < 23 then 21 else 38))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 39 else 38) else (if i.val < 27 then 38 else 38)) else (if i.val < 30 then (if i.val < 29 then 38 else 38) else (if i.val < 31 then 74 else 38))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 39 else 21) else (if i.val < 35 then 38 else 22)) else (if i.val < 38 then (if i.val < 37 then 38 else 38) else (if i.val < 39 then 40 else 70))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 71 else 38) else (if i.val < 43 then 21 else 38)) else (if i.val < 46 then (if i.val < 45 then 20 else 21) else (if i.val < 47 then 38 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 43 else 38) else (if i.val < 51 then 21 else 43)) else (if i.val < 54 then (if i.val < 53 then 72 else 21) else (if i.val < 55 then 38 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 21 else 38) else (if i.val < 59 then 21 else 72)) else (if i.val < 62 then (if i.val < 61 then 21 else 38) else (if i.val < 63 then 43 else 38)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 38 else 41) else (if i.val < 67 then 38 else 38)) else (if i.val < 70 then (if i.val < 69 then 22 else 22) else (if i.val < 71 then 22 else 21))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 38 else 38) else (if i.val < 75 then 21 else 41)) else (if i.val < 78 then (if i.val < 77 then 7 else 74) else (if i.val < 79 then 74 else 21)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 41) else (if i.val < 83 then 21 else 68)) else (if i.val < 86 then (if i.val < 85 then 38 else 40) else (if i.val < 87 then 41 else 73))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 21 else 38) else (if i.val < 91 then 21 else 71)) else (if i.val < 94 then (if i.val < 93 then 73 else 38) else (if i.val < 95 then 21 else 7))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 22 else 21) else (if i.val < 99 then 21 else 68)) else (if i.val < 102 then (if i.val < 101 then 21 else 38) else (if i.val < 103 then 72 else 68))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 43 else 75) else (if i.val < 107 then 22 else 21)) else (if i.val < 110 then (if i.val < 109 then 43 else 43) else (if i.val < 111 then 38 else 71)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 40 else 41) else (if i.val < 115 then 38 else 21)) else (if i.val < 118 then (if i.val < 117 then 38 else 41) else (if i.val < 119 then 22 else 43))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 38 else 43) else (if i.val < 123 then 40 else 21)) else (if i.val < 126 then (if i.val < 125 then 38 else 74) else (if i.val < 127 then 74 else 21))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 40 else 38) else (if i.val < 131 then 68 else 41)) else (if i.val < 134 then (if i.val < 133 then 73 else 73) else (if i.val < 135 then 38 else 7))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 74 else 22) else (if i.val < 139 then 21 else 21)) else (if i.val < 142 then (if i.val < 141 then 22 else 23) else (if i.val < 143 then 21 else 21)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 21 else 21) else (if i.val < 147 then 38 else 38)) else (if i.val < 150 then (if i.val < 149 then 21 else 38) else (if i.val < 151 then 5 else 75))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 73 else 75) else (if i.val < 155 then 42 else 73)) else (if i.val < 158 then (if i.val < 157 then 41 else 38) else (if i.val < 159 then 40 else 21))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 75 else 21) else (if i.val < 163 then 21 else 38)) else (if i.val < 166 then (if i.val < 165 then 20 else 41) else (if i.val < 167 then 43 else 22))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 21 else 39) else (if i.val < 171 then 39 else 38)) else (if i.val < 174 then (if i.val < 173 then 73 else 74) else (if i.val < 175 then 74 else 75)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 41 else 38) else (if i.val < 179 then 38 else 74)) else (if i.val < 182 then (if i.val < 181 then 21 else 38) else (if i.val < 183 then 74 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 38 else 70) else (if i.val < 187 then 38 else 68)) else (if i.val < 190 then (if i.val < 189 then 38 else 40) else (if i.val < 191 then 72 else 68)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 40 else 38) else (if i.val < 195 then 38 else 38)) else (if i.val < 198 then (if i.val < 197 then 42 else 73) else (if i.val < 199 then 73 else 73))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 38 else 40) else (if i.val < 203 then 75 else 38)) else (if i.val < 206 then (if i.val < 205 then 38 else 70) else (if i.val < 207 then 6 else 21)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 38 else 21) else (if i.val < 211 then 22 else 21)) else (if i.val < 214 then (if i.val < 213 then 38 else 38) else (if i.val < 215 then 38 else 21))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 73 else 21) else (if i.val < 219 then 21 else 74)) else (if i.val < 222 then (if i.val < 221 then 22 else 22) else (if i.val < 223 then 38 else 38))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 38 else 20) else (if i.val < 227 then 71 else 21)) else (if i.val < 230 then (if i.val < 229 then 21 else 22) else (if i.val < 231 then 38 else 22))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 21 else 38) else (if i.val < 235 then 73 else 43)) else (if i.val < 238 then (if i.val < 237 then 39 else 42) else (if i.val < 239 then 22 else 7)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 38 else 40) else (if i.val < 243 then 43 else 38)) else (if i.val < 246 then (if i.val < 245 then 38 else 20) else (if i.val < 247 then 71 else 38))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 70 else 41) else (if i.val < 251 then 38 else 71)) else (if i.val < 254 then (if i.val < 253 then 38 else 73) else (if i.val < 255 then 71 else 38))))))))

theorem g32p_supplierForest_actual_118 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_118 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_118 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_051491
  · exact g32p_supplierForest_actual_051493
  · exact g32p_supplierForest_actual_051496
  · exact g32p_supplierForest_actual_051504
  · exact g32p_supplierForest_actual_051528
  · exact g32p_supplierForest_actual_051544
  · exact g32p_supplierForest_actual_051581
  · exact g32p_supplierForest_actual_051613
  · exact g32p_supplierForest_actual_051619
  · exact g32p_supplierForest_actual_051675
  · exact g32p_supplierForest_actual_051684
  · exact g32p_supplierForest_actual_051767
  · exact g32p_supplierForest_actual_051874
  · exact g32p_supplierForest_actual_051936
  · exact g32p_supplierForest_actual_051962
  · exact g32p_supplierForest_actual_052058
  · exact g32p_supplierForest_actual_052059
  · exact g32p_supplierForest_actual_052062
  · exact g32p_supplierForest_actual_052086
  · exact g32p_supplierForest_actual_052089
  · exact g32p_supplierForest_actual_052092
  · exact g32p_supplierForest_actual_052104
  · exact g32p_supplierForest_actual_052114
  · exact g32p_supplierForest_actual_052131
  · exact g32p_supplierForest_actual_052143
  · exact g32p_supplierForest_actual_052147
  · exact g32p_supplierForest_actual_052227
  · exact g32p_supplierForest_actual_052256
  · exact g32p_supplierForest_actual_052284
  · exact g32p_supplierForest_actual_052303
  · exact g32p_supplierForest_actual_052365
  · exact g32p_supplierForest_actual_052394
  · exact g32p_supplierForest_actual_052481
  · exact g32p_supplierForest_actual_052598
  · exact g32p_supplierForest_actual_052661
  · exact g32p_supplierForest_actual_052665
  · exact g32p_supplierForest_actual_052707
  · exact g32p_supplierForest_actual_052719
  · exact g32p_supplierForest_actual_052740
  · exact g32p_supplierForest_actual_052802
  · exact g32p_supplierForest_actual_052811
  · exact g32p_supplierForest_actual_052813
  · exact g32p_supplierForest_actual_052864
  · exact g32p_supplierForest_actual_052940
  · exact g32p_supplierForest_actual_052949
  · exact g32p_supplierForest_actual_053026
  · exact g32p_supplierForest_actual_053031
  · exact g32p_supplierForest_actual_053170
  · exact g32p_supplierForest_actual_053172
  · exact g32p_supplierForest_actual_053188
  · exact g32p_supplierForest_actual_053297
  · exact g32p_supplierForest_actual_053313
  · exact g32p_supplierForest_actual_053325
  · exact g32p_supplierForest_actual_053372
  · exact g32p_supplierForest_actual_053415
  · exact g32p_supplierForest_actual_053454
  · exact g32p_supplierForest_actual_053461
  · exact g32p_supplierForest_actual_053489
  · exact g32p_supplierForest_actual_053514
  · exact g32p_supplierForest_actual_053533
  · exact g32p_supplierForest_actual_053538
  · exact g32p_supplierForest_actual_053580
  · exact g32p_supplierForest_actual_053584
  · exact g32p_supplierForest_actual_053604
  · exact g32p_supplierForest_actual_053616
  · exact g32p_supplierForest_actual_053619
  · exact g32p_supplierForest_actual_053637
  · exact g32p_supplierForest_actual_053647
  · exact g32p_supplierForest_actual_053655
  · exact g32p_supplierForest_actual_053673
  · exact g32p_supplierForest_actual_053685
  · exact g32p_supplierForest_actual_053717
  · exact g32p_supplierForest_actual_053733
  · exact g32p_supplierForest_actual_053786
  · exact g32p_supplierForest_actual_053806
  · exact g32p_supplierForest_actual_053921
  · exact g32p_supplierForest_actual_054000
  · exact g32p_supplierForest_actual_054043
  · exact g32p_supplierForest_actual_054065
  · exact g32p_supplierForest_actual_054084
  · exact g32p_supplierForest_actual_054085
  · exact g32p_supplierForest_actual_054107
  · exact g32p_supplierForest_actual_054110
  · exact g32p_supplierForest_actual_054159
  · exact g32p_supplierForest_actual_054166
  · exact g32p_supplierForest_actual_054182
  · exact g32p_supplierForest_actual_054200
  · exact g32p_supplierForest_actual_054209
  · exact g32p_supplierForest_actual_054269
  · exact g32p_supplierForest_actual_054275
  · exact g32p_supplierForest_actual_054370
  · exact g32p_supplierForest_actual_054381
  · exact g32p_supplierForest_actual_054432
  · exact g32p_supplierForest_actual_054452
  · exact g32p_supplierForest_actual_054591
  · exact g32p_supplierForest_actual_054640
  · exact g32p_supplierForest_actual_054653
  · exact g32p_supplierForest_actual_054658
  · exact g32p_supplierForest_actual_054707
  · exact g32p_supplierForest_actual_054722
  · exact g32p_supplierForest_actual_054781
  · exact g32p_supplierForest_actual_054782
  · exact g32p_supplierForest_actual_054803
  · exact g32p_supplierForest_actual_054815
  · exact g32p_supplierForest_actual_054832
  · exact g32p_supplierForest_actual_054834
  · exact g32p_supplierForest_actual_054901
  · exact g32p_supplierForest_actual_054977
  · exact g32p_supplierForest_actual_054978
  · exact g32p_supplierForest_actual_054994
  · exact g32p_supplierForest_actual_055027
  · exact g32p_supplierForest_actual_055078
  · exact g32p_supplierForest_actual_055118
  · exact g32p_supplierForest_actual_055123
  · exact g32p_supplierForest_actual_055130
  · exact g32p_supplierForest_actual_055151
  · exact g32p_supplierForest_actual_055158
  · exact g32p_supplierForest_actual_055181
  · exact g32p_supplierForest_actual_055186
  · exact g32p_supplierForest_actual_055194
  · exact g32p_supplierForest_actual_055201
  · exact g32p_supplierForest_actual_055213
  · exact g32p_supplierForest_actual_055230
  · exact g32p_supplierForest_actual_055278
  · exact g32p_supplierForest_actual_055306
  · exact g32p_supplierForest_actual_055330
  · exact g32p_supplierForest_actual_055345
  · exact g32p_supplierForest_actual_055367
  · exact g32p_supplierForest_actual_055416
  · exact g32p_supplierForest_actual_055420
  · exact g32p_supplierForest_actual_055424
  · exact g32p_supplierForest_actual_055465
  · exact g32p_supplierForest_actual_055474
  · exact g32p_supplierForest_actual_055476
  · exact g32p_supplierForest_actual_055485
  · exact g32p_supplierForest_actual_055513
  · exact g32p_supplierForest_actual_055587
  · exact g32p_supplierForest_actual_055596
  · exact g32p_supplierForest_actual_055660
  · exact g32p_supplierForest_actual_055663
  · exact g32p_supplierForest_actual_055671
  · exact g32p_supplierForest_actual_055688
  · exact g32p_supplierForest_actual_055755
  · exact g32p_supplierForest_actual_055765
  · exact g32p_supplierForest_actual_055772
  · exact g32p_supplierForest_actual_055774
  · exact g32p_supplierForest_actual_055781
  · exact g32p_supplierForest_actual_055814
  · exact g32p_supplierForest_actual_055863
  · exact g32p_supplierForest_actual_055876
  · exact g32p_supplierForest_actual_055896
  · exact g32p_supplierForest_actual_055925
  · exact g32p_supplierForest_actual_055980
  · exact g32p_supplierForest_actual_056033
  · exact g32p_supplierForest_actual_056111
  · exact g32p_supplierForest_actual_056131
  · exact g32p_supplierForest_actual_056158
  · exact g32p_supplierForest_actual_056159
  · exact g32p_supplierForest_actual_056161
  · exact g32p_supplierForest_actual_056177
  · exact g32p_supplierForest_actual_056184
  · exact g32p_supplierForest_actual_056202
  · exact g32p_supplierForest_actual_056229
  · exact g32p_supplierForest_actual_056290
  · exact g32p_supplierForest_actual_056309
  · exact g32p_supplierForest_actual_056405
  · exact g32p_supplierForest_actual_056434
  · exact g32p_supplierForest_actual_056511
  · exact g32p_supplierForest_actual_056547
  · exact g32p_supplierForest_actual_056559
  · exact g32p_supplierForest_actual_056599
  · exact g32p_supplierForest_actual_056738
  · exact g32p_supplierForest_actual_056780
  · exact g32p_supplierForest_actual_056806
  · exact g32p_supplierForest_actual_056840
  · exact g32p_supplierForest_actual_056854
  · exact g32p_supplierForest_actual_056935
  · exact g32p_supplierForest_actual_056938
  · exact g32p_supplierForest_actual_056993
  · exact g32p_supplierForest_actual_057022
  · exact g32p_supplierForest_actual_057027
  · exact g32p_supplierForest_actual_057036
  · exact g32p_supplierForest_actual_057172
  · exact g32p_supplierForest_actual_057198
  · exact g32p_supplierForest_actual_057242
  · exact g32p_supplierForest_actual_057287
  · exact g32p_supplierForest_actual_057323
  · exact g32p_supplierForest_actual_057361
  · exact g32p_supplierForest_actual_057400
  · exact g32p_supplierForest_actual_057419
  · exact g32p_supplierForest_actual_057435
  · exact g32p_supplierForest_actual_057488
  · exact g32p_supplierForest_actual_057512
  · exact g32p_supplierForest_actual_057513
  · exact g32p_supplierForest_actual_057519
  · exact g32p_supplierForest_actual_057522
  · exact g32p_supplierForest_actual_057534
  · exact g32p_supplierForest_actual_057541
  · exact g32p_supplierForest_actual_057578
  · exact g32p_supplierForest_actual_057586
  · exact g32p_supplierForest_actual_057605
  · exact g32p_supplierForest_actual_057615
  · exact g32p_supplierForest_actual_057633
  · exact g32p_supplierForest_actual_057672
  · exact g32p_supplierForest_actual_057702
  · exact g32p_supplierForest_actual_057708
  · exact g32p_supplierForest_actual_057713
  · exact g32p_supplierForest_actual_057738
  · exact g32p_supplierForest_actual_057741
  · exact g32p_supplierForest_actual_057775
  · exact g32p_supplierForest_actual_057780
  · exact g32p_supplierForest_actual_057799
  · exact g32p_supplierForest_actual_057823
  · exact g32p_supplierForest_actual_057878
  · exact g32p_supplierForest_actual_057903
  · exact g32p_supplierForest_actual_057905
  · exact g32p_supplierForest_actual_057947
  · exact g32p_supplierForest_actual_058026
  · exact g32p_supplierForest_actual_058067
  · exact g32p_supplierForest_actual_058093
  · exact g32p_supplierForest_actual_058137
  · exact g32p_supplierForest_actual_058143
  · exact g32p_supplierForest_actual_058191
  · exact g32p_supplierForest_actual_058199
  · exact g32p_supplierForest_actual_058242
  · exact g32p_supplierForest_actual_058285
  · exact g32p_supplierForest_actual_058309
  · exact g32p_supplierForest_actual_058318
  · exact g32p_supplierForest_actual_058337
  · exact g32p_supplierForest_actual_058360
  · exact g32p_supplierForest_actual_058375
  · exact g32p_supplierForest_actual_058383
  · exact g32p_supplierForest_actual_058501
  · exact g32p_supplierForest_actual_058532
  · exact g32p_supplierForest_actual_058539
  · exact g32p_supplierForest_actual_058562
  · exact g32p_supplierForest_actual_058575
  · exact g32p_supplierForest_actual_058662
  · exact g32p_supplierForest_actual_058733
  · exact g32p_supplierForest_actual_058752
  · exact g32p_supplierForest_actual_058753
  · exact g32p_supplierForest_actual_058832
  · exact g32p_supplierForest_actual_058861
  · exact g32p_supplierForest_actual_058864
  · exact g32p_supplierForest_actual_058880
  · exact g32p_supplierForest_actual_058899
  · exact g32p_supplierForest_actual_058903
  · exact g32p_supplierForest_actual_058905
  · exact g32p_supplierForest_actual_058934
  · exact g32p_supplierForest_actual_058958
  · exact g32p_supplierForest_actual_058963
  · exact g32p_supplierForest_actual_058992
  · exact g32p_supplierForest_actual_059002
  · exact g32p_supplierForest_actual_059011
  · exact g32p_supplierForest_actual_059018
  · exact g32p_supplierForest_actual_059022

def g32p_supplierForest_nodes_119 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_059049 else g32p_supplierForest_node_059096) else (if i.val < 3 then g32p_supplierForest_node_059139 else g32p_supplierForest_node_059224)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_059230 else g32p_supplierForest_node_059239) else (if i.val < 7 then g32p_supplierForest_node_059252 else g32p_supplierForest_node_059264))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_059325 else g32p_supplierForest_node_059362) else (if i.val < 11 then g32p_supplierForest_node_059415 else g32p_supplierForest_node_059442)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_059460 else g32p_supplierForest_node_059470) else (if i.val < 15 then g32p_supplierForest_node_059480 else g32p_supplierForest_node_059523)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_059529 else g32p_supplierForest_node_059589) else (if i.val < 19 then g32p_supplierForest_node_059593 else g32p_supplierForest_node_059614)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_059647 else g32p_supplierForest_node_059666) else (if i.val < 23 then g32p_supplierForest_node_059668 else g32p_supplierForest_node_059671))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_059688 else g32p_supplierForest_node_059690) else (if i.val < 27 then g32p_supplierForest_node_059724 else g32p_supplierForest_node_059764)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_059828 else g32p_supplierForest_node_059844) else (if i.val < 31 then g32p_supplierForest_node_059862 else g32p_supplierForest_node_059902))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_059916 else g32p_supplierForest_node_059930) else (if i.val < 35 then g32p_supplierForest_node_059938 else g32p_supplierForest_node_059946)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_060012 else g32p_supplierForest_node_060022) else (if i.val < 39 then g32p_supplierForest_node_060036 else g32p_supplierForest_node_060125))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_060132 else g32p_supplierForest_node_060145) else (if i.val < 43 then g32p_supplierForest_node_060160 else g32p_supplierForest_node_060163)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_060210 else g32p_supplierForest_node_060249) else (if i.val < 47 then g32p_supplierForest_node_060251 else g32p_supplierForest_node_060314)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_060382 else g32p_supplierForest_node_060415) else (if i.val < 51 then g32p_supplierForest_node_060419 else g32p_supplierForest_node_060420)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_060429 else g32p_supplierForest_node_060459) else (if i.val < 55 then g32p_supplierForest_node_060471 else g32p_supplierForest_node_060491))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_060501 else g32p_supplierForest_node_060561) else (if i.val < 59 then g32p_supplierForest_node_060717 else g32p_supplierForest_node_060742)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_060743 else g32p_supplierForest_node_060759) else (if i.val < 63 then g32p_supplierForest_node_060825 else g32p_supplierForest_node_060827)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_060847 else g32p_supplierForest_node_060858) else (if i.val < 67 then g32p_supplierForest_node_060897 else g32p_supplierForest_node_060918)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_060924 else g32p_supplierForest_node_060972) else (if i.val < 71 then g32p_supplierForest_node_060973 else g32p_supplierForest_node_061015))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_061080 else g32p_supplierForest_node_061085) else (if i.val < 75 then g32p_supplierForest_node_061098 else g32p_supplierForest_node_061123)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_061175 else g32p_supplierForest_node_061209) else (if i.val < 79 then g32p_supplierForest_node_061215 else g32p_supplierForest_node_061243)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_061244 else g32p_supplierForest_node_061265) else (if i.val < 83 then g32p_supplierForest_node_061296 else g32p_supplierForest_node_061322)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_061342 else g32p_supplierForest_node_061372) else (if i.val < 87 then g32p_supplierForest_node_061380 else g32p_supplierForest_node_061412))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_061457 else g32p_supplierForest_node_061473) else (if i.val < 91 then g32p_supplierForest_node_061489 else g32p_supplierForest_node_061495)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_061499 else g32p_supplierForest_node_061504) else (if i.val < 95 then g32p_supplierForest_node_061535 else g32p_supplierForest_node_061556))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_061603 else g32p_supplierForest_node_061609) else (if i.val < 99 then g32p_supplierForest_node_061620 else g32p_supplierForest_node_061713)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_061759 else g32p_supplierForest_node_061776) else (if i.val < 103 then g32p_supplierForest_node_061796 else g32p_supplierForest_node_061818))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_061857 else g32p_supplierForest_node_061905) else (if i.val < 107 then g32p_supplierForest_node_061985 else g32p_supplierForest_node_062033)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_062034 else g32p_supplierForest_node_062050) else (if i.val < 111 then g32p_supplierForest_node_062062 else g32p_supplierForest_node_062099)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_062172 else g32p_supplierForest_node_062190) else (if i.val < 115 then g32p_supplierForest_node_062213 else g32p_supplierForest_node_062250)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_062252 else g32p_supplierForest_node_062275) else (if i.val < 119 then g32p_supplierForest_node_062281 else g32p_supplierForest_node_062286))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_062353 else g32p_supplierForest_node_062356) else (if i.val < 123 then g32p_supplierForest_node_062381 else g32p_supplierForest_node_062464)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_062476 else g32p_supplierForest_node_062477) else (if i.val < 127 then g32p_supplierForest_node_062484 else g32p_supplierForest_node_062493))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_062552 else g32p_supplierForest_node_062562) else (if i.val < 131 then g32p_supplierForest_node_062570 else g32p_supplierForest_node_062578)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_062624 else g32p_supplierForest_node_062677) else (if i.val < 135 then g32p_supplierForest_node_062703 else g32p_supplierForest_node_062707))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_062722 else g32p_supplierForest_node_062766) else (if i.val < 139 then g32p_supplierForest_node_062771 else g32p_supplierForest_node_062777)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_062813 else g32p_supplierForest_node_062835) else (if i.val < 143 then g32p_supplierForest_node_062839 else g32p_supplierForest_node_062859)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_062867 else g32p_supplierForest_node_062884) else (if i.val < 147 then g32p_supplierForest_node_062911 else g32p_supplierForest_node_062914)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_062933 else g32p_supplierForest_node_063019) else (if i.val < 151 then g32p_supplierForest_node_063031 else g32p_supplierForest_node_063042))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_063068 else g32p_supplierForest_node_063072) else (if i.val < 155 then g32p_supplierForest_node_063080 else g32p_supplierForest_node_063137)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_063161 else g32p_supplierForest_node_063209) else (if i.val < 159 then g32p_supplierForest_node_063221 else g32p_supplierForest_node_063234))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_063283 else g32p_supplierForest_node_063285) else (if i.val < 163 then g32p_supplierForest_node_063296 else g32p_supplierForest_node_063404)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_063489 else g32p_supplierForest_node_063509) else (if i.val < 167 then g32p_supplierForest_node_063542 else g32p_supplierForest_node_063570))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_063648 else g32p_supplierForest_node_063657) else (if i.val < 171 then g32p_supplierForest_node_063734 else g32p_supplierForest_node_063779)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_063804 else g32p_supplierForest_node_063858) else (if i.val < 175 then g32p_supplierForest_node_063859 else g32p_supplierForest_node_063891)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_063909 else g32p_supplierForest_node_063916) else (if i.val < 179 then g32p_supplierForest_node_063935 else g32p_supplierForest_node_063947)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_063955 else g32p_supplierForest_node_064002) else (if i.val < 183 then g32p_supplierForest_node_064070 else g32p_supplierForest_node_064095))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_064099 else g32p_supplierForest_node_064107) else (if i.val < 187 then g32p_supplierForest_node_064108 else g32p_supplierForest_node_064117)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_064120 else g32p_supplierForest_node_064168) else (if i.val < 191 then g32p_supplierForest_node_064170 else g32p_supplierForest_node_064189)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_064198 else g32p_supplierForest_node_064309) else (if i.val < 195 then g32p_supplierForest_node_064337 else g32p_supplierForest_node_064383)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_064384 else g32p_supplierForest_node_064439) else (if i.val < 199 then g32p_supplierForest_node_064492 else g32p_supplierForest_node_064496))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_064511 else g32p_supplierForest_node_064515) else (if i.val < 203 then g32p_supplierForest_node_064542 else g32p_supplierForest_node_064572)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_064574 else g32p_supplierForest_node_064598) else (if i.val < 207 then g32p_supplierForest_node_064697 else g32p_supplierForest_node_064747)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_064754 else g32p_supplierForest_node_064761) else (if i.val < 211 then g32p_supplierForest_node_064770 else g32p_supplierForest_node_064778)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_064787 else g32p_supplierForest_node_064809) else (if i.val < 215 then g32p_supplierForest_node_064820 else g32p_supplierForest_node_064828))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_064857 else g32p_supplierForest_node_064867) else (if i.val < 219 then g32p_supplierForest_node_064942 else g32p_supplierForest_node_064974)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_064991 else g32p_supplierForest_node_065047) else (if i.val < 223 then g32p_supplierForest_node_065081 else g32p_supplierForest_node_065118))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_065165 else g32p_supplierForest_node_065185) else (if i.val < 227 then g32p_supplierForest_node_065236 else g32p_supplierForest_node_065244)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_065262 else g32p_supplierForest_node_065273) else (if i.val < 231 then g32p_supplierForest_node_065286 else g32p_supplierForest_node_065291))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_065319 else g32p_supplierForest_node_065339) else (if i.val < 235 then g32p_supplierForest_node_065362 else g32p_supplierForest_node_065444)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_065471 else g32p_supplierForest_node_065488) else (if i.val < 239 then g32p_supplierForest_node_065501 else g32p_supplierForest_node_065519)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_065537 else g32p_supplierForest_node_065538) else (if i.val < 243 then g32p_supplierForest_node_065556 else g32p_supplierForest_node_065558)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_065574 else g32p_supplierForest_node_065616) else (if i.val < 247 then g32p_supplierForest_node_065617 else g32p_supplierForest_node_065706))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_065734 else g32p_supplierForest_node_065747) else (if i.val < 251 then g32p_supplierForest_node_065768 else g32p_supplierForest_node_065779)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_065780 else g32p_supplierForest_node_065831) else (if i.val < 255 then g32p_supplierForest_node_065857 else g32p_supplierForest_node_065879))))))))

def g32p_supplierForest_classes_119 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 72 else 41) else (if i.val < 3 then 39 else 39)) else (if i.val < 6 then (if i.val < 5 then 38 else 40) else (if i.val < 7 then 22 else 38))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 41 else 21) else (if i.val < 11 then 38 else 38)) else (if i.val < 14 then (if i.val < 13 then 39 else 21) else (if i.val < 15 then 21 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 68 else 38) else (if i.val < 19 then 38 else 38)) else (if i.val < 22 then (if i.val < 21 then 21 else 38) else (if i.val < 23 then 38 else 22))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 21 else 42) else (if i.val < 27 then 38 else 21)) else (if i.val < 30 then (if i.val < 29 then 73 else 38) else (if i.val < 31 then 73 else 73))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 22) else (if i.val < 35 then 43 else 21)) else (if i.val < 38 then (if i.val < 37 then 41 else 73) else (if i.val < 39 then 40 else 43))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 43 else 39) else (if i.val < 43 then 22 else 38)) else (if i.val < 46 then (if i.val < 45 then 38 else 38) else (if i.val < 47 then 38 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 38 else 73) else (if i.val < 51 then 21 else 21)) else (if i.val < 54 then (if i.val < 53 then 22 else 71) else (if i.val < 55 then 21 else 22))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 71 else 38) else (if i.val < 59 then 71 else 42)) else (if i.val < 62 then (if i.val < 61 then 43 else 22) else (if i.val < 63 then 38 else 21)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 21 else 38) else (if i.val < 67 then 68 else 21)) else (if i.val < 70 then (if i.val < 69 then 43 else 21) else (if i.val < 71 then 21 else 68))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 38 else 38) else (if i.val < 75 then 73 else 74)) else (if i.val < 78 then (if i.val < 77 then 68 else 38) else (if i.val < 79 then 21 else 21)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 21) else (if i.val < 83 then 74 else 75)) else (if i.val < 86 then (if i.val < 85 then 38 else 40) else (if i.val < 87 then 74 else 39))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 38 else 43) else (if i.val < 91 then 21 else 72)) else (if i.val < 94 then (if i.val < 93 then 38 else 6) else (if i.val < 95 then 22 else 38))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 38 else 22) else (if i.val < 99 then 38 else 38)) else (if i.val < 102 then (if i.val < 101 then 39 else 22) else (if i.val < 103 then 41 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 6 else 22) else (if i.val < 107 then 38 else 40)) else (if i.val < 110 then (if i.val < 109 then 42 else 21) else (if i.val < 111 then 38 else 38)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 43) else (if i.val < 115 then 68 else 38)) else (if i.val < 118 then (if i.val < 117 then 21 else 73) else (if i.val < 119 then 38 else 43))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 75 else 38) else (if i.val < 123 then 38 else 38)) else (if i.val < 126 then (if i.val < 125 then 38 else 21) else (if i.val < 127 then 38 else 21))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 38 else 43) else (if i.val < 131 then 38 else 38)) else (if i.val < 134 then (if i.val < 133 then 21 else 40) else (if i.val < 135 then 22 else 73))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 21 else 21) else (if i.val < 139 then 73 else 38)) else (if i.val < 142 then (if i.val < 141 then 70 else 7) else (if i.val < 143 then 21 else 21)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 22 else 38) else (if i.val < 147 then 38 else 22)) else (if i.val < 150 then (if i.val < 149 then 38 else 22) else (if i.val < 151 then 21 else 21))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 38 else 74) else (if i.val < 155 then 21 else 22)) else (if i.val < 158 then (if i.val < 157 then 7 else 38) else (if i.val < 159 then 21 else 22))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 20 else 21) else (if i.val < 163 then 72 else 38)) else (if i.val < 166 then (if i.val < 165 then 72 else 42) else (if i.val < 167 then 38 else 38))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 21 else 38) else (if i.val < 171 then 41 else 21)) else (if i.val < 174 then (if i.val < 173 then 7 else 38) else (if i.val < 175 then 22 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 22 else 21) else (if i.val < 179 then 38 else 40)) else (if i.val < 182 then (if i.val < 181 then 21 else 38) else (if i.val < 183 then 38 else 21))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 21 else 38) else (if i.val < 187 then 72 else 38)) else (if i.val < 190 then (if i.val < 189 then 38 else 38) else (if i.val < 191 then 21 else 38)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 38 else 38) else (if i.val < 195 then 38 else 38)) else (if i.val < 198 then (if i.val < 197 then 43 else 74) else (if i.val < 199 then 74 else 74))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 75 else 74) else (if i.val < 203 then 38 else 38)) else (if i.val < 206 then (if i.val < 205 then 38 else 21) else (if i.val < 207 then 21 else 73)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 70 else 38) else (if i.val < 211 then 43 else 21)) else (if i.val < 214 then (if i.val < 213 then 38 else 38) else (if i.val < 215 then 22 else 42))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 21 else 68) else (if i.val < 219 then 40 else 21)) else (if i.val < 222 then (if i.val < 221 then 38 else 41) else (if i.val < 223 then 38 else 38))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 20 else 42) else (if i.val < 227 then 70 else 22)) else (if i.val < 230 then (if i.val < 229 then 41 else 21) else (if i.val < 231 then 22 else 41))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 21 else 41) else (if i.val < 235 then 22 else 74)) else (if i.val < 238 then (if i.val < 237 then 38 else 38) else (if i.val < 239 then 73 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 43 else 39) else (if i.val < 243 then 21 else 43)) else (if i.val < 246 then (if i.val < 245 then 38 else 21) else (if i.val < 247 then 68 else 38))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 73 else 38) else (if i.val < 251 then 21 else 38)) else (if i.val < 254 then (if i.val < 253 then 74 else 38) else (if i.val < 255 then 20 else 38))))))))

theorem g32p_supplierForest_actual_119 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_119 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_119 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_059049
  · exact g32p_supplierForest_actual_059096
  · exact g32p_supplierForest_actual_059139
  · exact g32p_supplierForest_actual_059224
  · exact g32p_supplierForest_actual_059230
  · exact g32p_supplierForest_actual_059239
  · exact g32p_supplierForest_actual_059252
  · exact g32p_supplierForest_actual_059264
  · exact g32p_supplierForest_actual_059325
  · exact g32p_supplierForest_actual_059362
  · exact g32p_supplierForest_actual_059415
  · exact g32p_supplierForest_actual_059442
  · exact g32p_supplierForest_actual_059460
  · exact g32p_supplierForest_actual_059470
  · exact g32p_supplierForest_actual_059480
  · exact g32p_supplierForest_actual_059523
  · exact g32p_supplierForest_actual_059529
  · exact g32p_supplierForest_actual_059589
  · exact g32p_supplierForest_actual_059593
  · exact g32p_supplierForest_actual_059614
  · exact g32p_supplierForest_actual_059647
  · exact g32p_supplierForest_actual_059666
  · exact g32p_supplierForest_actual_059668
  · exact g32p_supplierForest_actual_059671
  · exact g32p_supplierForest_actual_059688
  · exact g32p_supplierForest_actual_059690
  · exact g32p_supplierForest_actual_059724
  · exact g32p_supplierForest_actual_059764
  · exact g32p_supplierForest_actual_059828
  · exact g32p_supplierForest_actual_059844
  · exact g32p_supplierForest_actual_059862
  · exact g32p_supplierForest_actual_059902
  · exact g32p_supplierForest_actual_059916
  · exact g32p_supplierForest_actual_059930
  · exact g32p_supplierForest_actual_059938
  · exact g32p_supplierForest_actual_059946
  · exact g32p_supplierForest_actual_060012
  · exact g32p_supplierForest_actual_060022
  · exact g32p_supplierForest_actual_060036
  · exact g32p_supplierForest_actual_060125
  · exact g32p_supplierForest_actual_060132
  · exact g32p_supplierForest_actual_060145
  · exact g32p_supplierForest_actual_060160
  · exact g32p_supplierForest_actual_060163
  · exact g32p_supplierForest_actual_060210
  · exact g32p_supplierForest_actual_060249
  · exact g32p_supplierForest_actual_060251
  · exact g32p_supplierForest_actual_060314
  · exact g32p_supplierForest_actual_060382
  · exact g32p_supplierForest_actual_060415
  · exact g32p_supplierForest_actual_060419
  · exact g32p_supplierForest_actual_060420
  · exact g32p_supplierForest_actual_060429
  · exact g32p_supplierForest_actual_060459
  · exact g32p_supplierForest_actual_060471
  · exact g32p_supplierForest_actual_060491
  · exact g32p_supplierForest_actual_060501
  · exact g32p_supplierForest_actual_060561
  · exact g32p_supplierForest_actual_060717
  · exact g32p_supplierForest_actual_060742
  · exact g32p_supplierForest_actual_060743
  · exact g32p_supplierForest_actual_060759
  · exact g32p_supplierForest_actual_060825
  · exact g32p_supplierForest_actual_060827
  · exact g32p_supplierForest_actual_060847
  · exact g32p_supplierForest_actual_060858
  · exact g32p_supplierForest_actual_060897
  · exact g32p_supplierForest_actual_060918
  · exact g32p_supplierForest_actual_060924
  · exact g32p_supplierForest_actual_060972
  · exact g32p_supplierForest_actual_060973
  · exact g32p_supplierForest_actual_061015
  · exact g32p_supplierForest_actual_061080
  · exact g32p_supplierForest_actual_061085
  · exact g32p_supplierForest_actual_061098
  · exact g32p_supplierForest_actual_061123
  · exact g32p_supplierForest_actual_061175
  · exact g32p_supplierForest_actual_061209
  · exact g32p_supplierForest_actual_061215
  · exact g32p_supplierForest_actual_061243
  · exact g32p_supplierForest_actual_061244
  · exact g32p_supplierForest_actual_061265
  · exact g32p_supplierForest_actual_061296
  · exact g32p_supplierForest_actual_061322
  · exact g32p_supplierForest_actual_061342
  · exact g32p_supplierForest_actual_061372
  · exact g32p_supplierForest_actual_061380
  · exact g32p_supplierForest_actual_061412
  · exact g32p_supplierForest_actual_061457
  · exact g32p_supplierForest_actual_061473
  · exact g32p_supplierForest_actual_061489
  · exact g32p_supplierForest_actual_061495
  · exact g32p_supplierForest_actual_061499
  · exact g32p_supplierForest_actual_061504
  · exact g32p_supplierForest_actual_061535
  · exact g32p_supplierForest_actual_061556
  · exact g32p_supplierForest_actual_061603
  · exact g32p_supplierForest_actual_061609
  · exact g32p_supplierForest_actual_061620
  · exact g32p_supplierForest_actual_061713
  · exact g32p_supplierForest_actual_061759
  · exact g32p_supplierForest_actual_061776
  · exact g32p_supplierForest_actual_061796
  · exact g32p_supplierForest_actual_061818
  · exact g32p_supplierForest_actual_061857
  · exact g32p_supplierForest_actual_061905
  · exact g32p_supplierForest_actual_061985
  · exact g32p_supplierForest_actual_062033
  · exact g32p_supplierForest_actual_062034
  · exact g32p_supplierForest_actual_062050
  · exact g32p_supplierForest_actual_062062
  · exact g32p_supplierForest_actual_062099
  · exact g32p_supplierForest_actual_062172
  · exact g32p_supplierForest_actual_062190
  · exact g32p_supplierForest_actual_062213
  · exact g32p_supplierForest_actual_062250
  · exact g32p_supplierForest_actual_062252
  · exact g32p_supplierForest_actual_062275
  · exact g32p_supplierForest_actual_062281
  · exact g32p_supplierForest_actual_062286
  · exact g32p_supplierForest_actual_062353
  · exact g32p_supplierForest_actual_062356
  · exact g32p_supplierForest_actual_062381
  · exact g32p_supplierForest_actual_062464
  · exact g32p_supplierForest_actual_062476
  · exact g32p_supplierForest_actual_062477
  · exact g32p_supplierForest_actual_062484
  · exact g32p_supplierForest_actual_062493
  · exact g32p_supplierForest_actual_062552
  · exact g32p_supplierForest_actual_062562
  · exact g32p_supplierForest_actual_062570
  · exact g32p_supplierForest_actual_062578
  · exact g32p_supplierForest_actual_062624
  · exact g32p_supplierForest_actual_062677
  · exact g32p_supplierForest_actual_062703
  · exact g32p_supplierForest_actual_062707
  · exact g32p_supplierForest_actual_062722
  · exact g32p_supplierForest_actual_062766
  · exact g32p_supplierForest_actual_062771
  · exact g32p_supplierForest_actual_062777
  · exact g32p_supplierForest_actual_062813
  · exact g32p_supplierForest_actual_062835
  · exact g32p_supplierForest_actual_062839
  · exact g32p_supplierForest_actual_062859
  · exact g32p_supplierForest_actual_062867
  · exact g32p_supplierForest_actual_062884
  · exact g32p_supplierForest_actual_062911
  · exact g32p_supplierForest_actual_062914
  · exact g32p_supplierForest_actual_062933
  · exact g32p_supplierForest_actual_063019
  · exact g32p_supplierForest_actual_063031
  · exact g32p_supplierForest_actual_063042
  · exact g32p_supplierForest_actual_063068
  · exact g32p_supplierForest_actual_063072
  · exact g32p_supplierForest_actual_063080
  · exact g32p_supplierForest_actual_063137
  · exact g32p_supplierForest_actual_063161
  · exact g32p_supplierForest_actual_063209
  · exact g32p_supplierForest_actual_063221
  · exact g32p_supplierForest_actual_063234
  · exact g32p_supplierForest_actual_063283
  · exact g32p_supplierForest_actual_063285
  · exact g32p_supplierForest_actual_063296
  · exact g32p_supplierForest_actual_063404
  · exact g32p_supplierForest_actual_063489
  · exact g32p_supplierForest_actual_063509
  · exact g32p_supplierForest_actual_063542
  · exact g32p_supplierForest_actual_063570
  · exact g32p_supplierForest_actual_063648
  · exact g32p_supplierForest_actual_063657
  · exact g32p_supplierForest_actual_063734
  · exact g32p_supplierForest_actual_063779
  · exact g32p_supplierForest_actual_063804
  · exact g32p_supplierForest_actual_063858
  · exact g32p_supplierForest_actual_063859
  · exact g32p_supplierForest_actual_063891
  · exact g32p_supplierForest_actual_063909
  · exact g32p_supplierForest_actual_063916
  · exact g32p_supplierForest_actual_063935
  · exact g32p_supplierForest_actual_063947
  · exact g32p_supplierForest_actual_063955
  · exact g32p_supplierForest_actual_064002
  · exact g32p_supplierForest_actual_064070
  · exact g32p_supplierForest_actual_064095
  · exact g32p_supplierForest_actual_064099
  · exact g32p_supplierForest_actual_064107
  · exact g32p_supplierForest_actual_064108
  · exact g32p_supplierForest_actual_064117
  · exact g32p_supplierForest_actual_064120
  · exact g32p_supplierForest_actual_064168
  · exact g32p_supplierForest_actual_064170
  · exact g32p_supplierForest_actual_064189
  · exact g32p_supplierForest_actual_064198
  · exact g32p_supplierForest_actual_064309
  · exact g32p_supplierForest_actual_064337
  · exact g32p_supplierForest_actual_064383
  · exact g32p_supplierForest_actual_064384
  · exact g32p_supplierForest_actual_064439
  · exact g32p_supplierForest_actual_064492
  · exact g32p_supplierForest_actual_064496
  · exact g32p_supplierForest_actual_064511
  · exact g32p_supplierForest_actual_064515
  · exact g32p_supplierForest_actual_064542
  · exact g32p_supplierForest_actual_064572
  · exact g32p_supplierForest_actual_064574
  · exact g32p_supplierForest_actual_064598
  · exact g32p_supplierForest_actual_064697
  · exact g32p_supplierForest_actual_064747
  · exact g32p_supplierForest_actual_064754
  · exact g32p_supplierForest_actual_064761
  · exact g32p_supplierForest_actual_064770
  · exact g32p_supplierForest_actual_064778
  · exact g32p_supplierForest_actual_064787
  · exact g32p_supplierForest_actual_064809
  · exact g32p_supplierForest_actual_064820
  · exact g32p_supplierForest_actual_064828
  · exact g32p_supplierForest_actual_064857
  · exact g32p_supplierForest_actual_064867
  · exact g32p_supplierForest_actual_064942
  · exact g32p_supplierForest_actual_064974
  · exact g32p_supplierForest_actual_064991
  · exact g32p_supplierForest_actual_065047
  · exact g32p_supplierForest_actual_065081
  · exact g32p_supplierForest_actual_065118
  · exact g32p_supplierForest_actual_065165
  · exact g32p_supplierForest_actual_065185
  · exact g32p_supplierForest_actual_065236
  · exact g32p_supplierForest_actual_065244
  · exact g32p_supplierForest_actual_065262
  · exact g32p_supplierForest_actual_065273
  · exact g32p_supplierForest_actual_065286
  · exact g32p_supplierForest_actual_065291
  · exact g32p_supplierForest_actual_065319
  · exact g32p_supplierForest_actual_065339
  · exact g32p_supplierForest_actual_065362
  · exact g32p_supplierForest_actual_065444
  · exact g32p_supplierForest_actual_065471
  · exact g32p_supplierForest_actual_065488
  · exact g32p_supplierForest_actual_065501
  · exact g32p_supplierForest_actual_065519
  · exact g32p_supplierForest_actual_065537
  · exact g32p_supplierForest_actual_065538
  · exact g32p_supplierForest_actual_065556
  · exact g32p_supplierForest_actual_065558
  · exact g32p_supplierForest_actual_065574
  · exact g32p_supplierForest_actual_065616
  · exact g32p_supplierForest_actual_065617
  · exact g32p_supplierForest_actual_065706
  · exact g32p_supplierForest_actual_065734
  · exact g32p_supplierForest_actual_065747
  · exact g32p_supplierForest_actual_065768
  · exact g32p_supplierForest_actual_065779
  · exact g32p_supplierForest_actual_065780
  · exact g32p_supplierForest_actual_065831
  · exact g32p_supplierForest_actual_065857
  · exact g32p_supplierForest_actual_065879

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_065882 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065882 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065882 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069212 := by
  decide +kernel

theorem g32p_supplierForest_actual_065882 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065882) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065882
    g32p_supplierForest_actual_069212

def g32p_supplierForest_node_065890 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065890 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065890 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132720 := by
  decide +kernel

theorem g32p_supplierForest_actual_065890 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065890) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_065890
    g32p_supplierForest_actual_132720

def g32p_supplierForest_node_065919 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065919 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065919 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068976 := by
  decide +kernel

theorem g32p_supplierForest_actual_065919 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065919) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_065919
    g32p_supplierForest_actual_068976

def g32p_supplierForest_node_065940 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_065940 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065940 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131360 := by
  decide +kernel

theorem g32p_supplierForest_actual_065940 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065940) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_065940
    g32p_supplierForest_actual_131360

def g32p_supplierForest_node_066037 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066037 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066037 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070812 := by
  decide +kernel

theorem g32p_supplierForest_actual_066037 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066037) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_066037
    g32p_supplierForest_actual_070812

def g32p_supplierForest_node_066047 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066047 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066047 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131445 := by
  decide +kernel

theorem g32p_supplierForest_actual_066047 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066047) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 0 g32p_supplierForest_edge_066047
    g32p_supplierForest_actual_131445

def g32p_supplierForest_node_066060 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066060 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066060 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_136827 := by
  decide +kernel

theorem g32p_supplierForest_actual_066060 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066060) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_066060
    g32p_supplierForest_actual_136827

def g32p_supplierForest_node_066068 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066068 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066068 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132851 := by
  decide +kernel

theorem g32p_supplierForest_actual_066068 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066068) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 0 g32p_supplierForest_edge_066068
    g32p_supplierForest_actual_132851

def g32p_supplierForest_node_066140 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066140 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066140 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065329 := by
  decide +kernel

theorem g32p_supplierForest_actual_066140 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066140) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_066140
    g32p_supplierForest_actual_065329

def g32p_supplierForest_node_066169 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066169 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010382 := by
  decide +kernel

theorem g32p_supplierForest_actual_066169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066169) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_066169
    g32p_supplierForest_actual_010382

def g32p_supplierForest_node_066204 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066204 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066204 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065342 := by
  decide +kernel

theorem g32p_supplierForest_actual_066204 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066204) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_066204
    g32p_supplierForest_actual_065342

def g32p_supplierForest_node_066232 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066232 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066232 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011121 := by
  decide +kernel

theorem g32p_supplierForest_actual_066232 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066232) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_066232
    g32p_supplierForest_actual_011121

def g32p_supplierForest_node_066257 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066257 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066257 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_137623 := by
  decide +kernel

theorem g32p_supplierForest_actual_066257 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066257) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 2 g32p_supplierForest_edge_066257
    g32p_supplierForest_actual_137623

def g32p_supplierForest_node_066258 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066258 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066258 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_129508 := by
  decide +kernel

theorem g32p_supplierForest_actual_066258 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066258) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_066258
    g32p_supplierForest_actual_129508

def g32p_supplierForest_node_066279 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066279 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066279 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132033 := by
  decide +kernel

theorem g32p_supplierForest_actual_066279 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066279) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_066279
    g32p_supplierForest_actual_132033

def g32p_supplierForest_node_066308 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066308 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066308 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_065794 := by
  decide +kernel

theorem g32p_supplierForest_actual_066308 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066308) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_066308
    g32p_supplierForest_actual_065794

def g32p_supplierForest_node_066341 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066341 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068797 := by
  decide +kernel

theorem g32p_supplierForest_actual_066341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066341) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_066341
    g32p_supplierForest_actual_068797

def g32p_supplierForest_node_066362 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066362 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_142234 := by
  decide +kernel

theorem g32p_supplierForest_actual_066362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066362) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 2 g32p_supplierForest_edge_066362
    g32p_supplierForest_actual_142234

def g32p_supplierForest_node_066375 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066375 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066375 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_133112 := by
  decide +kernel

theorem g32p_supplierForest_actual_066375 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066375) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 0 g32p_supplierForest_edge_066375
    g32p_supplierForest_actual_133112

def g32p_supplierForest_node_066398 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066398 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066398 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056580 := by
  decide +kernel

theorem g32p_supplierForest_actual_066398 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066398) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_066398
    g32p_supplierForest_actual_056580

def g32p_supplierForest_node_066399 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066399 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066399 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_137243 := by
  decide +kernel

theorem g32p_supplierForest_actual_066399 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066399) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_066399
    g32p_supplierForest_actual_137243

def g32p_supplierForest_node_066411 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_066411 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066411 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045714 := by
  decide +kernel

theorem g32p_supplierForest_actual_066411 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066411) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 3 g32p_supplierForest_edge_066411
    g32p_supplierForest_actual_045714

def g32p_supplierForest_node_066435 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066435 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066435 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062189 := by
  decide +kernel

theorem g32p_supplierForest_actual_066435 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066435) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_066435
    g32p_supplierForest_actual_062189

def g32p_supplierForest_node_066464 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066464 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066464 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_066556 := by
  decide +kernel

theorem g32p_supplierForest_actual_066464 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066464) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_066464
    g32p_supplierForest_actual_066556

def g32p_supplierForest_node_066519 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066519 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066519 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_008639 := by
  decide +kernel

theorem g32p_supplierForest_actual_066519 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066519) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_066519
    g32p_supplierForest_actual_008639

def g32p_supplierForest_node_066524 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066524 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066524 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060448 := by
  decide +kernel

theorem g32p_supplierForest_actual_066524 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066524) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_066524
    g32p_supplierForest_actual_060448

def g32p_supplierForest_node_066598 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066598 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_066601 := by
  decide +kernel

theorem g32p_supplierForest_actual_066598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066598) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_066598
    g32p_supplierForest_actual_066601

def g32p_supplierForest_node_066628 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066628 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066628 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_134798 := by
  decide +kernel

theorem g32p_supplierForest_actual_066628 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066628) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_066628
    g32p_supplierForest_actual_134798

def g32p_supplierForest_node_066630 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066630 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066630 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061253 := by
  decide +kernel

theorem g32p_supplierForest_actual_066630 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066630) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_066630
    g32p_supplierForest_actual_061253

def g32p_supplierForest_node_066632 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066632 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066632 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061269 := by
  decide +kernel

theorem g32p_supplierForest_actual_066632 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066632) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_066632
    g32p_supplierForest_actual_061269

def g32p_supplierForest_node_066658 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066658 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066658 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061242 := by
  decide +kernel

theorem g32p_supplierForest_actual_066658 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066658) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_066658
    g32p_supplierForest_actual_061242

def g32p_supplierForest_node_066662 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066662 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066662 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_144189 := by
  decide +kernel

theorem g32p_supplierForest_actual_066662 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066662) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 2 g32p_supplierForest_edge_066662
    g32p_supplierForest_actual_144189

def g32p_supplierForest_node_066678 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066678 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066678 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128983 := by
  decide +kernel

theorem g32p_supplierForest_actual_066678 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066678) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_066678
    g32p_supplierForest_actual_128983

def g32p_supplierForest_node_066689 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066689 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066689 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132746 := by
  decide +kernel

theorem g32p_supplierForest_actual_066689 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066689) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_066689
    g32p_supplierForest_actual_132746

def g32p_supplierForest_node_066690 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066690 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066690 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_130311 := by
  decide +kernel

theorem g32p_supplierForest_actual_066690 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066690) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_066690
    g32p_supplierForest_actual_130311

def g32p_supplierForest_node_066722 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066722 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066722 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132854 := by
  decide +kernel

theorem g32p_supplierForest_actual_066722 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066722) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 0 g32p_supplierForest_edge_066722
    g32p_supplierForest_actual_132854

def g32p_supplierForest_node_066724 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066724 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066724 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061569 := by
  decide +kernel

theorem g32p_supplierForest_actual_066724 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066724) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_066724
    g32p_supplierForest_actual_061569

def g32p_supplierForest_node_066785 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066785 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051775 := by
  decide +kernel

theorem g32p_supplierForest_actual_066785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066785) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_066785
    g32p_supplierForest_actual_051775

def g32p_supplierForest_node_066793 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066793 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066793 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_050941 := by
  decide +kernel

theorem g32p_supplierForest_actual_066793 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066793) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_066793
    g32p_supplierForest_actual_050941

def g32p_supplierForest_node_066822 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066822 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066822 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048786 := by
  decide +kernel

theorem g32p_supplierForest_actual_066822 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066822) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_066822
    g32p_supplierForest_actual_048786

def g32p_supplierForest_node_066831 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066831 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066831 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051370 := by
  decide +kernel

theorem g32p_supplierForest_actual_066831 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066831) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_066831
    g32p_supplierForest_actual_051370

def g32p_supplierForest_node_066840 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066840 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066840 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_044960 := by
  decide +kernel

theorem g32p_supplierForest_actual_066840 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066840) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_066840
    g32p_supplierForest_actual_044960

def g32p_supplierForest_node_066880 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_066880 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066880 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070846 := by
  decide +kernel

theorem g32p_supplierForest_actual_066880 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066880) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_066880
    g32p_supplierForest_actual_070846

def g32p_supplierForest_node_066938 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066938 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066938 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045070 := by
  decide +kernel

theorem g32p_supplierForest_actual_066938 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066938) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_066938
    g32p_supplierForest_actual_045070

def g32p_supplierForest_node_066966 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066966 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066966 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_133637 := by
  decide +kernel

theorem g32p_supplierForest_actual_066966 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066966) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_066966
    g32p_supplierForest_actual_133637

def g32p_supplierForest_node_067011 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067011 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067011 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132890 := by
  decide +kernel

theorem g32p_supplierForest_actual_067011 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067011) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_067011
    g32p_supplierForest_actual_132890

def g32p_supplierForest_node_067021 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067021 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067021 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131809 := by
  decide +kernel

theorem g32p_supplierForest_actual_067021 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067021) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_067021
    g32p_supplierForest_actual_131809

def g32p_supplierForest_node_067029 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067029 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067029 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050209 := by
  decide +kernel

theorem g32p_supplierForest_actual_067029 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067029) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_067029
    g32p_supplierForest_actual_050209

def g32p_supplierForest_node_067035 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067035 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067035 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071104 := by
  decide +kernel

theorem g32p_supplierForest_actual_067035 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067035) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_067035
    g32p_supplierForest_actual_071104

def g32p_supplierForest_node_067077 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067077 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067077 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_065166 := by
  decide +kernel

theorem g32p_supplierForest_actual_067077 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067077) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_067077
    g32p_supplierForest_actual_065166

def g32p_supplierForest_node_067079 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067079 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067079 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065607 := by
  decide +kernel

theorem g32p_supplierForest_actual_067079 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067079) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_067079
    g32p_supplierForest_actual_065607

def g32p_supplierForest_node_067115 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067115 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067115 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_050209 := by
  decide +kernel

theorem g32p_supplierForest_actual_067115 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067115) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_067115
    g32p_supplierForest_actual_050209

def g32p_supplierForest_node_067137 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067137 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067137 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_052774 := by
  decide +kernel

theorem g32p_supplierForest_actual_067137 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067137) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_067137
    g32p_supplierForest_actual_052774

def g32p_supplierForest_node_067163 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067163 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067163 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071310 := by
  decide +kernel

theorem g32p_supplierForest_actual_067163 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067163) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_067163
    g32p_supplierForest_actual_071310

def g32p_supplierForest_node_067178 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067178 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067178 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071337 := by
  decide +kernel

theorem g32p_supplierForest_actual_067178 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067178) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_067178
    g32p_supplierForest_actual_071337

def g32p_supplierForest_node_067196 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067196 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067196 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_133850 := by
  decide +kernel

theorem g32p_supplierForest_actual_067196 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067196) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_067196
    g32p_supplierForest_actual_133850

def g32p_supplierForest_node_067286 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067286 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067286 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_066449 := by
  decide +kernel

theorem g32p_supplierForest_actual_067286 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067286) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_067286
    g32p_supplierForest_actual_066449

def g32p_supplierForest_node_067303 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067303 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067303 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_061715 := by
  decide +kernel

theorem g32p_supplierForest_actual_067303 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067303) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_067303
    g32p_supplierForest_actual_061715

def g32p_supplierForest_node_067360 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067360 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070085 := by
  decide +kernel

theorem g32p_supplierForest_actual_067360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067360) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_067360
    g32p_supplierForest_actual_070085

def g32p_supplierForest_node_067372 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067372 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_062671 := by
  decide +kernel

theorem g32p_supplierForest_actual_067372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067372) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_067372
    g32p_supplierForest_actual_062671

def g32p_supplierForest_node_067463 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_067463 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067463 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_011038 := by
  decide +kernel

theorem g32p_supplierForest_actual_067463 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067463) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_067463
    g32p_supplierForest_actual_011038

def g32p_supplierForest_node_067481 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067481 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067481 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_060403 := by
  decide +kernel

theorem g32p_supplierForest_actual_067481 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067481) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_067481
    g32p_supplierForest_actual_060403

def g32p_supplierForest_node_067484 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067484 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067484 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044507 := by
  decide +kernel

theorem g32p_supplierForest_actual_067484 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067484) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_067484
    g32p_supplierForest_actual_044507

def g32p_supplierForest_node_067546 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067546 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067546 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_134147 := by
  decide +kernel

theorem g32p_supplierForest_actual_067546 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067546) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_067546
    g32p_supplierForest_actual_134147

def g32p_supplierForest_node_067669 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067669 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050349 := by
  decide +kernel

theorem g32p_supplierForest_actual_067669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067669) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_067669
    g32p_supplierForest_actual_050349

def g32p_supplierForest_node_067688 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067688 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067688 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009091 := by
  decide +kernel

theorem g32p_supplierForest_actual_067688 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067688) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_067688
    g32p_supplierForest_actual_009091

def g32p_supplierForest_node_067738 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067738 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_141573 := by
  decide +kernel

theorem g32p_supplierForest_actual_067738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067738) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_067738
    g32p_supplierForest_actual_141573

def g32p_supplierForest_node_067790 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067790 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067790 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070026 := by
  decide +kernel

theorem g32p_supplierForest_actual_067790 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067790) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_067790
    g32p_supplierForest_actual_070026

def g32p_supplierForest_node_067804 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067804 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067804 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_049696 := by
  decide +kernel

theorem g32p_supplierForest_actual_067804 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067804) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_067804
    g32p_supplierForest_actual_049696

def g32p_supplierForest_node_067830 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067830 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067830 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062999 := by
  decide +kernel

theorem g32p_supplierForest_actual_067830 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067830) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_067830
    g32p_supplierForest_actual_062999

def g32p_supplierForest_node_067910 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067910 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067910 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063343 := by
  decide +kernel

theorem g32p_supplierForest_actual_067910 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067910) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_067910
    g32p_supplierForest_actual_063343

def g32p_supplierForest_node_067920 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067920 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067920 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062821 := by
  decide +kernel

theorem g32p_supplierForest_actual_067920 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067920) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_067920
    g32p_supplierForest_actual_062821

def g32p_supplierForest_node_067933 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067933 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067933 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_048338 := by
  decide +kernel

theorem g32p_supplierForest_actual_067933 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067933) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_067933
    g32p_supplierForest_actual_048338

def g32p_supplierForest_node_068013 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068013 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068013 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_132323 := by
  decide +kernel

theorem g32p_supplierForest_actual_068013 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068013) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_068013
    g32p_supplierForest_actual_132323

def g32p_supplierForest_node_068015 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_068015 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068015 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063725 := by
  decide +kernel

theorem g32p_supplierForest_actual_068015 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068015) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_068015
    g32p_supplierForest_actual_063725

def g32p_supplierForest_node_068021 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068021 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068021 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_139681 := by
  decide +kernel

theorem g32p_supplierForest_actual_068021 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068021) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_068021
    g32p_supplierForest_actual_139681

def g32p_supplierForest_node_068053 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068053 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068053 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_135886 := by
  decide +kernel

theorem g32p_supplierForest_actual_068053 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068053) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_068053
    g32p_supplierForest_actual_135886

def g32p_supplierForest_node_068113 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068113 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_143449 := by
  decide +kernel

theorem g32p_supplierForest_actual_068113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068113) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_068113
    g32p_supplierForest_actual_143449

def g32p_supplierForest_node_068129 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068129 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068129 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_048350 := by
  decide +kernel

theorem g32p_supplierForest_actual_068129 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068129) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 2 g32p_supplierForest_edge_068129
    g32p_supplierForest_actual_048350

def g32p_supplierForest_node_068215 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068215 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068215 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_134190 := by
  decide +kernel

theorem g32p_supplierForest_actual_068215 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068215) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_068215
    g32p_supplierForest_actual_134190

def g32p_supplierForest_node_068253 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068253 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068253 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047735 := by
  decide +kernel

theorem g32p_supplierForest_actual_068253 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068253) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_068253
    g32p_supplierForest_actual_047735

def g32p_supplierForest_node_068281 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068281 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068281 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066887 := by
  decide +kernel

theorem g32p_supplierForest_actual_068281 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068281) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_068281
    g32p_supplierForest_actual_066887

def g32p_supplierForest_node_068283 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068283 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068283 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064835 := by
  decide +kernel

theorem g32p_supplierForest_actual_068283 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068283) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_068283
    g32p_supplierForest_actual_064835

def g32p_supplierForest_node_068285 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068285 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068285 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010790 := by
  decide +kernel

theorem g32p_supplierForest_actual_068285 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068285) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_068285
    g32p_supplierForest_actual_010790

def g32p_supplierForest_node_068319 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068319 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_142414 := by
  decide +kernel

theorem g32p_supplierForest_actual_068319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068319) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_068319
    g32p_supplierForest_actual_142414

def g32p_supplierForest_node_068327 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068327 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_059731 := by
  decide +kernel

theorem g32p_supplierForest_actual_068327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068327) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_068327
    g32p_supplierForest_actual_059731

def g32p_supplierForest_node_068358 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068358 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068358 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_139428 := by
  decide +kernel

theorem g32p_supplierForest_actual_068358 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068358) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_068358
    g32p_supplierForest_actual_139428

def g32p_supplierForest_node_068372 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068372 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051690 := by
  decide +kernel

theorem g32p_supplierForest_actual_068372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068372) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_068372
    g32p_supplierForest_actual_051690

def g32p_supplierForest_node_068465 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068465 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068465 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070502 := by
  decide +kernel

theorem g32p_supplierForest_actual_068465 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068465) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_068465
    g32p_supplierForest_actual_070502

def g32p_supplierForest_node_068473 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068473 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_134901 := by
  decide +kernel

theorem g32p_supplierForest_actual_068473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068473) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_068473
    g32p_supplierForest_actual_134901

def g32p_supplierForest_node_068500 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068500 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068500 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_131438 := by
  decide +kernel

theorem g32p_supplierForest_actual_068500 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068500) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_068500
    g32p_supplierForest_actual_131438

def g32p_supplierForest_node_068538 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068538 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068538 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129337 := by
  decide +kernel

theorem g32p_supplierForest_actual_068538 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068538) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_068538
    g32p_supplierForest_actual_129337

def g32p_supplierForest_node_068672 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068672 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068672 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128447 := by
  decide +kernel

theorem g32p_supplierForest_actual_068672 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068672) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_068672
    g32p_supplierForest_actual_128447

def g32p_supplierForest_node_068703 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_068703 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068703 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064016 := by
  decide +kernel

theorem g32p_supplierForest_actual_068703 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068703) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_068703
    g32p_supplierForest_actual_064016

def g32p_supplierForest_node_068720 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068720 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068720 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055150 := by
  decide +kernel

theorem g32p_supplierForest_actual_068720 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068720) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_068720
    g32p_supplierForest_actual_055150

def g32p_supplierForest_node_068734 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068734 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068734 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_045870 := by
  decide +kernel

theorem g32p_supplierForest_actual_068734 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068734) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_068734
    g32p_supplierForest_actual_045870

def g32p_supplierForest_node_068747 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068747 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068747 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_135283 := by
  decide +kernel

theorem g32p_supplierForest_actual_068747 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068747) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 3 g32p_supplierForest_edge_068747
    g32p_supplierForest_actual_135283

def g32p_supplierForest_node_068757 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068757 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068757 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_135093 := by
  decide +kernel

theorem g32p_supplierForest_actual_068757 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068757) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_068757
    g32p_supplierForest_actual_135093

def g32p_supplierForest_node_068763 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068763 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068763 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_068889 := by
  decide +kernel

theorem g32p_supplierForest_actual_068763 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068763) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_068763
    g32p_supplierForest_actual_068889

def g32p_supplierForest_node_068785 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068785 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_135123 := by
  decide +kernel

theorem g32p_supplierForest_actual_068785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068785) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_068785
    g32p_supplierForest_actual_135123

def g32p_supplierForest_node_068791 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068791 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068791 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_135217 := by
  decide +kernel

theorem g32p_supplierForest_actual_068791 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068791) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_068791
    g32p_supplierForest_actual_135217

def g32p_supplierForest_node_068802 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068802 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068802 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_048855 := by
  decide +kernel

theorem g32p_supplierForest_actual_068802 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068802) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_068802
    g32p_supplierForest_actual_048855

def g32p_supplierForest_node_068831 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068831 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068831 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067788 := by
  decide +kernel

theorem g32p_supplierForest_actual_068831 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068831) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_068831
    g32p_supplierForest_actual_067788

def g32p_supplierForest_node_068843 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068843 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068843 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_135700 := by
  decide +kernel

theorem g32p_supplierForest_actual_068843 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068843) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_068843
    g32p_supplierForest_actual_135700

def g32p_supplierForest_node_068855 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068855 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068855 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_129355 := by
  decide +kernel

theorem g32p_supplierForest_actual_068855 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068855) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_068855
    g32p_supplierForest_actual_129355

def g32p_supplierForest_node_068886 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068886 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068886 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132509 := by
  decide +kernel

theorem g32p_supplierForest_actual_068886 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068886) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_068886
    g32p_supplierForest_actual_132509

def g32p_supplierForest_node_068942 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_068942 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068942 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068832 := by
  decide +kernel

theorem g32p_supplierForest_actual_068942 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068942) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_068942
    g32p_supplierForest_actual_068832

def g32p_supplierForest_node_069010 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069010 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069010 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_010961 := by
  decide +kernel

theorem g32p_supplierForest_actual_069010 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069010) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_069010
    g32p_supplierForest_actual_010961

def g32p_supplierForest_node_069041 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_069041 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069041 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_054701 := by
  decide +kernel

theorem g32p_supplierForest_actual_069041 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069041) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_069041
    g32p_supplierForest_actual_054701

def g32p_supplierForest_node_069055 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069055 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069055 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_065732 := by
  decide +kernel

theorem g32p_supplierForest_actual_069055 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069055) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_069055
    g32p_supplierForest_actual_065732

def g32p_supplierForest_node_069064 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069064 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069064 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132249 := by
  decide +kernel

theorem g32p_supplierForest_actual_069064 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069064) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_069064
    g32p_supplierForest_actual_132249

def g32p_supplierForest_node_069100 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069100 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069100 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047126 := by
  decide +kernel

theorem g32p_supplierForest_actual_069100 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069100) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_069100
    g32p_supplierForest_actual_047126

def g32p_supplierForest_node_069162 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069162 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069162 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060866 := by
  decide +kernel

theorem g32p_supplierForest_actual_069162 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069162) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_069162
    g32p_supplierForest_actual_060866

def g32p_supplierForest_node_069170 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_069170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069170 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057592 := by
  decide +kernel

theorem g32p_supplierForest_actual_069170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069170) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_069170
    g32p_supplierForest_actual_057592

def g32p_supplierForest_node_069180 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_069180 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069180 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_006373 := by
  decide +kernel

theorem g32p_supplierForest_actual_069180 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069180) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_069180
    g32p_supplierForest_actual_006373

def g32p_supplierForest_node_069197 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069197 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069197 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_135439 := by
  decide +kernel

theorem g32p_supplierForest_actual_069197 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069197) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_069197
    g32p_supplierForest_actual_135439

def g32p_supplierForest_node_069252 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_069252 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069252 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_047337 := by
  decide +kernel

theorem g32p_supplierForest_actual_069252 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069252) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_069252
    g32p_supplierForest_actual_047337

def g32p_supplierForest_node_069256 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069256 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069256 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069765 := by
  decide +kernel

theorem g32p_supplierForest_actual_069256 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069256) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_069256
    g32p_supplierForest_actual_069765

def g32p_supplierForest_node_069296 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_069296 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069296 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_130605 := by
  decide +kernel

theorem g32p_supplierForest_actual_069296 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069296) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_069296
    g32p_supplierForest_actual_130605

def g32p_supplierForest_node_069306 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_069306 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069306 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_133330 := by
  decide +kernel

theorem g32p_supplierForest_actual_069306 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069306) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_069306
    g32p_supplierForest_actual_133330

def g32p_supplierForest_node_069356 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069356 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069356 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011178 := by
  decide +kernel

theorem g32p_supplierForest_actual_069356 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069356) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_069356
    g32p_supplierForest_actual_011178

def g32p_supplierForest_node_069421 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069421 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_068772 := by
  decide +kernel

theorem g32p_supplierForest_actual_069421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069421) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_069421
    g32p_supplierForest_actual_068772

def g32p_supplierForest_node_069463 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_069463 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069463 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070297 := by
  decide +kernel

theorem g32p_supplierForest_actual_069463 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069463) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_069463
    g32p_supplierForest_actual_070297

def g32p_supplierForest_node_069464 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069464 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069464 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_047508 := by
  decide +kernel

theorem g32p_supplierForest_actual_069464 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069464) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_069464
    g32p_supplierForest_actual_047508

def g32p_supplierForest_node_069511 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069511 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047996 := by
  decide +kernel

theorem g32p_supplierForest_actual_069511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069511) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_069511
    g32p_supplierForest_actual_047996

def g32p_supplierForest_node_069614 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_069614 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069614 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050328 := by
  decide +kernel

theorem g32p_supplierForest_actual_069614 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069614) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_069614
    g32p_supplierForest_actual_050328

def g32p_supplierForest_node_069635 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_069635 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069635 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_011851 := by
  decide +kernel

theorem g32p_supplierForest_actual_069635 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069635) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_069635
    g32p_supplierForest_actual_011851

def g32p_supplierForest_node_069667 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069667 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069667 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055099 := by
  decide +kernel

theorem g32p_supplierForest_actual_069667 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069667) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_069667
    g32p_supplierForest_actual_055099

def g32p_supplierForest_node_069695 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069695 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069695 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_135700 := by
  decide +kernel

theorem g32p_supplierForest_actual_069695 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069695) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_069695
    g32p_supplierForest_actual_135700

def g32p_supplierForest_node_069697 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069697 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069697 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_060601 := by
  decide +kernel

theorem g32p_supplierForest_actual_069697 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069697) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_069697
    g32p_supplierForest_actual_060601

def g32p_supplierForest_node_069708 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069708 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069708 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057087 := by
  decide +kernel

theorem g32p_supplierForest_actual_069708 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069708) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_069708
    g32p_supplierForest_actual_057087

def g32p_supplierForest_node_069874 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_069874 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069874 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_054783 := by
  decide +kernel

theorem g32p_supplierForest_actual_069874 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069874) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_069874
    g32p_supplierForest_actual_054783

def g32p_supplierForest_node_069895 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069895 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069895 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_068148 := by
  decide +kernel

theorem g32p_supplierForest_actual_069895 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069895) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_069895
    g32p_supplierForest_actual_068148

def g32p_supplierForest_node_069907 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069907 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069907 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071215 := by
  decide +kernel

theorem g32p_supplierForest_actual_069907 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069907) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_069907
    g32p_supplierForest_actual_071215

def g32p_supplierForest_node_069946 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069946 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069946 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_135947 := by
  decide +kernel

theorem g32p_supplierForest_actual_069946 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069946) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_069946
    g32p_supplierForest_actual_135947

def g32p_supplierForest_node_069956 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_069956 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069956 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_054454 := by
  decide +kernel

theorem g32p_supplierForest_actual_069956 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069956) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_069956
    g32p_supplierForest_actual_054454

def g32p_supplierForest_node_070004 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_070004 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070004 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_052241 := by
  decide +kernel

theorem g32p_supplierForest_actual_070004 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070004) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 1 g32p_supplierForest_edge_070004
    g32p_supplierForest_actual_052241

def g32p_supplierForest_node_070045 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070045 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070045 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_138370 := by
  decide +kernel

theorem g32p_supplierForest_actual_070045 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070045) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_070045
    g32p_supplierForest_actual_138370

def g32p_supplierForest_node_070103 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070103 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070103 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_068226 := by
  decide +kernel

theorem g32p_supplierForest_actual_070103 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070103) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_070103
    g32p_supplierForest_actual_068226

def g32p_supplierForest_node_070108 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_070108 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070108 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_049796 := by
  decide +kernel

theorem g32p_supplierForest_actual_070108 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070108) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_070108
    g32p_supplierForest_actual_049796

def g32p_supplierForest_node_070126 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_070126 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070126 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011115 := by
  decide +kernel

theorem g32p_supplierForest_actual_070126 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070126) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_070126
    g32p_supplierForest_actual_011115

def g32p_supplierForest_node_070147 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070147 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070147 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_132656 := by
  decide +kernel

theorem g32p_supplierForest_actual_070147 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070147) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_070147
    g32p_supplierForest_actual_132656

def g32p_supplierForest_node_070162 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_070162 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070162 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060334 := by
  decide +kernel

theorem g32p_supplierForest_actual_070162 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070162) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_070162
    g32p_supplierForest_actual_060334

def g32p_supplierForest_node_070189 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_070189 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070189 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_006105 := by
  decide +kernel

theorem g32p_supplierForest_actual_070189 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070189) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_070189
    g32p_supplierForest_actual_006105

def g32p_supplierForest_node_070195 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070195 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070195 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_006290 := by
  decide +kernel

theorem g32p_supplierForest_actual_070195 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070195) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_070195
    g32p_supplierForest_actual_006290

def g32p_supplierForest_node_070305 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_070305 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070305 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050024 := by
  decide +kernel

theorem g32p_supplierForest_actual_070305 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070305) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_070305
    g32p_supplierForest_actual_050024

def g32p_supplierForest_node_070327 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_070327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070327 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_132708 := by
  decide +kernel

theorem g32p_supplierForest_actual_070327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070327) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_070327
    g32p_supplierForest_actual_132708

def g32p_supplierForest_node_070329 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_070329 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070329 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_142414 := by
  decide +kernel

theorem g32p_supplierForest_actual_070329 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070329) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_070329
    g32p_supplierForest_actual_142414

def g32p_supplierForest_node_070343 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_070343 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070343 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132761 := by
  decide +kernel

theorem g32p_supplierForest_actual_070343 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070343) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_070343
    g32p_supplierForest_actual_132761

def g32p_supplierForest_node_070359 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_070359 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070359 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048161 := by
  decide +kernel

theorem g32p_supplierForest_actual_070359 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070359) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_070359
    g32p_supplierForest_actual_048161

def g32p_supplierForest_node_070398 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_070398 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070398 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_050556 := by
  decide +kernel

theorem g32p_supplierForest_actual_070398 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070398) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_070398
    g32p_supplierForest_actual_050556

def g32p_supplierForest_node_070500 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070500 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070500 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_135513 := by
  decide +kernel

theorem g32p_supplierForest_actual_070500 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070500) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_070500
    g32p_supplierForest_actual_135513

def g32p_supplierForest_node_070519 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070519 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070519 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_049152 := by
  decide +kernel

theorem g32p_supplierForest_actual_070519 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070519) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_070519
    g32p_supplierForest_actual_049152

def g32p_supplierForest_node_070524 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070524 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070524 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_131544 := by
  decide +kernel

theorem g32p_supplierForest_actual_070524 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070524) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_070524
    g32p_supplierForest_actual_131544

def g32p_supplierForest_node_070527 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_070527 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070527 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_143682 := by
  decide +kernel

theorem g32p_supplierForest_actual_070527 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070527) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_070527
    g32p_supplierForest_actual_143682

def g32p_supplierForest_node_070534 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_070534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070534 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_059073 := by
  decide +kernel

theorem g32p_supplierForest_actual_070534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070534) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_070534
    g32p_supplierForest_actual_059073

def g32p_supplierForest_node_070557 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_070557 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070557 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048931 := by
  decide +kernel

theorem g32p_supplierForest_actual_070557 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070557) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_070557
    g32p_supplierForest_actual_048931

def g32p_supplierForest_node_070678 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070678 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070678 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_054551 := by
  decide +kernel

theorem g32p_supplierForest_actual_070678 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070678) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_070678
    g32p_supplierForest_actual_054551

def g32p_supplierForest_node_070686 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070686 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069996 := by
  decide +kernel

theorem g32p_supplierForest_actual_070686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070686) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_070686
    g32p_supplierForest_actual_069996

def g32p_supplierForest_node_070695 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_070695 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070695 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066390 := by
  decide +kernel

theorem g32p_supplierForest_actual_070695 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070695) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_070695
    g32p_supplierForest_actual_066390

def g32p_supplierForest_node_070696 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_070696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070696 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066900 := by
  decide +kernel

theorem g32p_supplierForest_actual_070696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070696) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_070696
    g32p_supplierForest_actual_066900

def g32p_supplierForest_node_070813 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_070813 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070813 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_140312 := by
  decide +kernel

theorem g32p_supplierForest_actual_070813 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070813) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_070813
    g32p_supplierForest_actual_140312

def g32p_supplierForest_node_070880 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_070880 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070880 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_143713 := by
  decide +kernel

theorem g32p_supplierForest_actual_070880 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070880) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_070880
    g32p_supplierForest_actual_143713

def g32p_supplierForest_node_070901 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070901 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070901 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_132590 := by
  decide +kernel

theorem g32p_supplierForest_actual_070901 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070901) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_070901
    g32p_supplierForest_actual_132590

def g32p_supplierForest_node_070946 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_070946 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070946 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_130484 := by
  decide +kernel

theorem g32p_supplierForest_actual_070946 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070946) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_070946
    g32p_supplierForest_actual_130484

def g32p_supplierForest_node_070952 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_070952 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070952 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_142594 := by
  decide +kernel

theorem g32p_supplierForest_actual_070952 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070952) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_070952
    g32p_supplierForest_actual_142594

def g32p_supplierForest_node_070975 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_070975 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070975 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_128621 := by
  decide +kernel

theorem g32p_supplierForest_actual_070975 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070975) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_070975
    g32p_supplierForest_actual_128621

def g32p_supplierForest_node_071051 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071051 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071051 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_058306 := by
  decide +kernel

theorem g32p_supplierForest_actual_071051 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071051) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_071051
    g32p_supplierForest_actual_058306

def g32p_supplierForest_node_071062 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_071062 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071062 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053111 := by
  decide +kernel

theorem g32p_supplierForest_actual_071062 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071062) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 3 g32p_supplierForest_edge_071062
    g32p_supplierForest_actual_053111

def g32p_supplierForest_node_071069 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071069 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071069 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_058985 := by
  decide +kernel

theorem g32p_supplierForest_actual_071069 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071069) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 3 g32p_supplierForest_edge_071069
    g32p_supplierForest_actual_058985

def g32p_supplierForest_node_071082 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_071082 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071082 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_046580 := by
  decide +kernel

theorem g32p_supplierForest_actual_071082 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071082) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_071082
    g32p_supplierForest_actual_046580

def g32p_supplierForest_node_071102 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_071102 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071102 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_062638 := by
  decide +kernel

theorem g32p_supplierForest_actual_071102 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071102) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_071102
    g32p_supplierForest_actual_062638

def g32p_supplierForest_node_071123 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071123 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071123 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_130850 := by
  decide +kernel

theorem g32p_supplierForest_actual_071123 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071123) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_071123
    g32p_supplierForest_actual_130850

def g32p_supplierForest_node_071164 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_071164 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071164 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_056797 := by
  decide +kernel

theorem g32p_supplierForest_actual_071164 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071164) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_071164
    g32p_supplierForest_actual_056797

def g32p_supplierForest_node_071168 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_071168 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071168 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069309 := by
  decide +kernel

theorem g32p_supplierForest_actual_071168 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071168) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_071168
    g32p_supplierForest_actual_069309

def g32p_supplierForest_node_071197 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_071197 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071197 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_140234 := by
  decide +kernel

theorem g32p_supplierForest_actual_071197 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071197) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_071197
    g32p_supplierForest_actual_140234

def g32p_supplierForest_node_071207 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071207 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071207 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010754 := by
  decide +kernel

theorem g32p_supplierForest_actual_071207 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071207) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_071207
    g32p_supplierForest_actual_010754

def g32p_supplierForest_node_071280 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071280 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071280 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_068797 := by
  decide +kernel

theorem g32p_supplierForest_actual_071280 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071280) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_071280
    g32p_supplierForest_actual_068797

def g32p_supplierForest_node_071305 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071305 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071305 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_068874 := by
  decide +kernel

theorem g32p_supplierForest_actual_071305 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071305) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_071305
    g32p_supplierForest_actual_068874

def g32p_supplierForest_node_071313 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071313 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071313 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_068899 := by
  decide +kernel

theorem g32p_supplierForest_actual_071313 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071313) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_071313
    g32p_supplierForest_actual_068899

def g32p_supplierForest_node_071340 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071340 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071340 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_135053 := by
  decide +kernel

theorem g32p_supplierForest_actual_071340 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071340) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_071340
    g32p_supplierForest_actual_135053

def g32p_supplierForest_node_071343 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_071343 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071343 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064127 := by
  decide +kernel

theorem g32p_supplierForest_actual_071343 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071343) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 2 g32p_supplierForest_edge_071343
    g32p_supplierForest_actual_064127

def g32p_supplierForest_node_071345 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071345 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071345 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011217 := by
  decide +kernel

theorem g32p_supplierForest_actual_071345 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071345) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_071345
    g32p_supplierForest_actual_011217

def g32p_supplierForest_node_071359 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_071359 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071359 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055169 := by
  decide +kernel

theorem g32p_supplierForest_actual_071359 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071359) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_071359
    g32p_supplierForest_actual_055169

def g32p_supplierForest_node_071387 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_071387 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071387 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065694 := by
  decide +kernel

theorem g32p_supplierForest_actual_071387 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071387) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_071387
    g32p_supplierForest_actual_065694

def g32p_supplierForest_node_071431 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071431 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071431 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047334 := by
  decide +kernel

theorem g32p_supplierForest_actual_071431 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071431) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_071431
    g32p_supplierForest_actual_047334

def g32p_supplierForest_node_071492 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_071492 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071492 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068278 := by
  decide +kernel

theorem g32p_supplierForest_actual_071492 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071492) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_071492
    g32p_supplierForest_actual_068278

def g32p_supplierForest_node_071498 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071498 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071498 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_060353 := by
  decide +kernel

theorem g32p_supplierForest_actual_071498 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071498) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_071498
    g32p_supplierForest_actual_060353

def g32p_supplierForest_node_071503 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_071503 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071503 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_139931 := by
  decide +kernel

theorem g32p_supplierForest_actual_071503 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071503) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_071503
    g32p_supplierForest_actual_139931

def g32p_supplierForest_node_071511 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071511 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_053019 := by
  decide +kernel

theorem g32p_supplierForest_actual_071511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071511) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_071511
    g32p_supplierForest_actual_053019

def g32p_supplierForest_node_071528 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_071528 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071528 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_055099 := by
  decide +kernel

theorem g32p_supplierForest_actual_071528 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071528) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_071528
    g32p_supplierForest_actual_055099

def g32p_supplierForest_node_071650 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071650 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071650 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067224 := by
  decide +kernel

theorem g32p_supplierForest_actual_071650 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071650) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_071650
    g32p_supplierForest_actual_067224

def g32p_supplierForest_node_071703 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071703 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071703 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_140713 := by
  decide +kernel

theorem g32p_supplierForest_actual_071703 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071703) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_071703
    g32p_supplierForest_actual_140713

def g32p_supplierForest_node_071787 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_071787 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071787 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081476 := by
  decide +kernel

theorem g32p_supplierForest_actual_071787 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071787) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 0 g32p_supplierForest_edge_071787
    g32p_supplierForest_actual_081476

def g32p_supplierForest_node_071801 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_071801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071801 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012487 := by
  decide +kernel

theorem g32p_supplierForest_actual_071801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071801) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_071801
    g32p_supplierForest_actual_012487

def g32p_supplierForest_node_071863 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071863 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071863 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094243 := by
  decide +kernel

theorem g32p_supplierForest_actual_071863 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071863) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_071863
    g32p_supplierForest_actual_094243

def g32p_supplierForest_node_071881 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_071881 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071881 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086591 := by
  decide +kernel

theorem g32p_supplierForest_actual_071881 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071881) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_071881
    g32p_supplierForest_actual_086591

def g32p_supplierForest_node_071886 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071886 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071886 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081613 := by
  decide +kernel

theorem g32p_supplierForest_actual_071886 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071886) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_071886
    g32p_supplierForest_actual_081613

def g32p_supplierForest_node_071906 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_071906 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071906 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081648 := by
  decide +kernel

theorem g32p_supplierForest_actual_071906 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071906) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_071906
    g32p_supplierForest_actual_081648

def g32p_supplierForest_node_071923 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071923 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071923 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081679 := by
  decide +kernel

theorem g32p_supplierForest_actual_071923 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071923) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_071923
    g32p_supplierForest_actual_081679

def g32p_supplierForest_node_071936 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_071936 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071936 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_074251 := by
  decide +kernel

theorem g32p_supplierForest_actual_071936 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071936) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_071936
    g32p_supplierForest_actual_074251

def g32p_supplierForest_node_071982 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_071982 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071982 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081623 := by
  decide +kernel

theorem g32p_supplierForest_actual_071982 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071982) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_071982
    g32p_supplierForest_actual_081623

def g32p_supplierForest_node_071988 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_071988 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071988 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012438 := by
  decide +kernel

theorem g32p_supplierForest_actual_071988 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071988) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_071988
    g32p_supplierForest_actual_012438

def g32p_supplierForest_node_072004 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_072004 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072004 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072550 := by
  decide +kernel

theorem g32p_supplierForest_actual_072004 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072004) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_072004
    g32p_supplierForest_actual_072550

def g32p_supplierForest_node_072007 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_072007 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072007 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086128 := by
  decide +kernel

theorem g32p_supplierForest_actual_072007 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072007) ∧
        IsConj g (g32p_literalRepresentative 45) := by
  exact g32p_archive_step_lift _ _ 45 2 g32p_supplierForest_edge_072007
    g32p_supplierForest_actual_086128

def g32p_supplierForest_node_072011 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072011 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072011 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014324 := by
  decide +kernel

theorem g32p_supplierForest_actual_072011 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072011) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_072011
    g32p_supplierForest_actual_014324

def g32p_supplierForest_node_072046 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072046 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072046 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082031 := by
  decide +kernel

theorem g32p_supplierForest_actual_072046 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072046) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 3 g32p_supplierForest_edge_072046
    g32p_supplierForest_actual_082031

def g32p_supplierForest_node_072083 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072083 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072083 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012770 := by
  decide +kernel

theorem g32p_supplierForest_actual_072083 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072083) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 2 g32p_supplierForest_edge_072083
    g32p_supplierForest_actual_012770

def g32p_supplierForest_node_072104 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072104 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072104 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_087021 := by
  decide +kernel

theorem g32p_supplierForest_actual_072104 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072104) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 3 g32p_supplierForest_edge_072104
    g32p_supplierForest_actual_087021

def g32p_supplierForest_node_072135 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_072135 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072135 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081964 := by
  decide +kernel

theorem g32p_supplierForest_actual_072135 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072135) ∧
        IsConj g (g32p_literalRepresentative 52) := by
  exact g32p_archive_step_lift _ _ 52 0 g32p_supplierForest_edge_072135
    g32p_supplierForest_actual_081964

def g32p_supplierForest_node_072166 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_072166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072166 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086936 := by
  decide +kernel

theorem g32p_supplierForest_actual_072166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072166) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_072166
    g32p_supplierForest_actual_086936

def g32p_supplierForest_node_072170 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_072170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072170 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096712 := by
  decide +kernel

theorem g32p_supplierForest_actual_072170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072170) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 2 g32p_supplierForest_edge_072170
    g32p_supplierForest_actual_096712

def g32p_supplierForest_node_072281 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_072281 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072281 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078778 := by
  decide +kernel

theorem g32p_supplierForest_actual_072281 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072281) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_072281
    g32p_supplierForest_actual_078778

def g32p_supplierForest_node_072298 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_072298 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072298 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_079200 := by
  decide +kernel

theorem g32p_supplierForest_actual_072298 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072298) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072298
    g32p_supplierForest_actual_079200

def g32p_supplierForest_node_072306 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_072306 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072306 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_013177 := by
  decide +kernel

theorem g32p_supplierForest_actual_072306 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072306) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_072306
    g32p_supplierForest_actual_013177

def g32p_supplierForest_node_072318 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_072318 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072318 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014440 := by
  decide +kernel

theorem g32p_supplierForest_actual_072318 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072318) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_072318
    g32p_supplierForest_actual_014440

def g32p_supplierForest_node_072364 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_072364 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072364 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082146 := by
  decide +kernel

theorem g32p_supplierForest_actual_072364 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072364) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072364
    g32p_supplierForest_actual_082146

def g32p_supplierForest_node_072367 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_072367 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072367 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_084317 := by
  decide +kernel

theorem g32p_supplierForest_actual_072367 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072367) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_072367
    g32p_supplierForest_actual_084317

def g32p_supplierForest_node_072424 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072424 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072424 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073112 := by
  decide +kernel

theorem g32p_supplierForest_actual_072424 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072424) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 3 g32p_supplierForest_edge_072424
    g32p_supplierForest_actual_073112

def g32p_supplierForest_node_072471 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_072471 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072471 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_091180 := by
  decide +kernel

theorem g32p_supplierForest_actual_072471 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072471) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_072471
    g32p_supplierForest_actual_091180

def g32p_supplierForest_node_072478 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072478 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072478 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023977 := by
  decide +kernel

theorem g32p_supplierForest_actual_072478 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072478) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072478
    g32p_supplierForest_actual_023977

def g32p_supplierForest_node_072565 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_072565 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072565 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082512 := by
  decide +kernel

theorem g32p_supplierForest_actual_072565 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072565) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_072565
    g32p_supplierForest_actual_082512

def g32p_supplierForest_node_072597 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072597 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072597 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_079945 := by
  decide +kernel

theorem g32p_supplierForest_actual_072597 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072597) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_072597
    g32p_supplierForest_actual_079945

def g32p_supplierForest_node_072621 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072621 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_020919 := by
  decide +kernel

theorem g32p_supplierForest_actual_072621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072621) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_072621
    g32p_supplierForest_actual_020919

def g32p_supplierForest_node_072656 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072656 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072656 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012462 := by
  decide +kernel

theorem g32p_supplierForest_actual_072656 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072656) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 1 g32p_supplierForest_edge_072656
    g32p_supplierForest_actual_012462

def g32p_supplierForest_node_072674 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072674 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072674 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096296 := by
  decide +kernel

theorem g32p_supplierForest_actual_072674 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072674) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_072674
    g32p_supplierForest_actual_096296

def g32p_supplierForest_node_072677 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_072677 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072677 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021236 := by
  decide +kernel

theorem g32p_supplierForest_actual_072677 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072677) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_072677
    g32p_supplierForest_actual_021236

def g32p_supplierForest_node_072678 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072678 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072678 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_091156 := by
  decide +kernel

theorem g32p_supplierForest_actual_072678 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072678) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_072678
    g32p_supplierForest_actual_091156

def g32p_supplierForest_node_072690 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_072690 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072690 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082764 := by
  decide +kernel

theorem g32p_supplierForest_actual_072690 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072690) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_072690
    g32p_supplierForest_actual_082764

def g32p_supplierForest_node_072712 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072712 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072712 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096984 := by
  decide +kernel

theorem g32p_supplierForest_actual_072712 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072712) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_072712
    g32p_supplierForest_actual_096984

def g32p_supplierForest_node_072725 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_072725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072725 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082745 := by
  decide +kernel

theorem g32p_supplierForest_actual_072725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072725) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_072725
    g32p_supplierForest_actual_082745

def g32p_supplierForest_node_072747 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_072747 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072747 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072743 := by
  decide +kernel

theorem g32p_supplierForest_actual_072747 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072747) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_072747
    g32p_supplierForest_actual_072743

def g32p_supplierForest_node_072748 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072748 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072748 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082031 := by
  decide +kernel

theorem g32p_supplierForest_actual_072748 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072748) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 0 g32p_supplierForest_edge_072748
    g32p_supplierForest_actual_082031

def g32p_supplierForest_node_072845 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_072845 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072845 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022010 := by
  decide +kernel

theorem g32p_supplierForest_actual_072845 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072845) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_072845
    g32p_supplierForest_actual_022010

def g32p_supplierForest_node_072852 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072852 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072852 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098798 := by
  decide +kernel

theorem g32p_supplierForest_actual_072852 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072852) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_072852
    g32p_supplierForest_actual_098798

def g32p_supplierForest_node_072869 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072869 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072869 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075950 := by
  decide +kernel

theorem g32p_supplierForest_actual_072869 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072869) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_072869
    g32p_supplierForest_actual_075950

def g32p_supplierForest_node_072908 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_072908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072908 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076075 := by
  decide +kernel

theorem g32p_supplierForest_actual_072908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072908) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_072908
    g32p_supplierForest_actual_076075

def g32p_supplierForest_node_072911 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072911 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072911 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072906 := by
  decide +kernel

theorem g32p_supplierForest_actual_072911 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072911) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_072911
    g32p_supplierForest_actual_072906

def g32p_supplierForest_node_072948 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_072948 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072948 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_012519 := by
  decide +kernel

theorem g32p_supplierForest_actual_072948 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072948) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_072948
    g32p_supplierForest_actual_012519

def g32p_supplierForest_node_072973 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_072973 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072973 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146789 := by
  decide +kernel

theorem g32p_supplierForest_actual_072973 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072973) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_072973
    g32p_supplierForest_actual_146789

def g32p_supplierForest_node_072980 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_072980 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072980 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083053 := by
  decide +kernel

theorem g32p_supplierForest_actual_072980 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072980) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072980
    g32p_supplierForest_actual_083053

def g32p_supplierForest_node_073013 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073013 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073013 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082343 := by
  decide +kernel

theorem g32p_supplierForest_actual_073013 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073013) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_073013
    g32p_supplierForest_actual_082343

def g32p_supplierForest_node_073038 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073038 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073038 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083427 := by
  decide +kernel

theorem g32p_supplierForest_actual_073038 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073038) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_073038
    g32p_supplierForest_actual_083427

def g32p_supplierForest_node_073056 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_073056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073056 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_098304 := by
  decide +kernel

theorem g32p_supplierForest_actual_073056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073056) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_073056
    g32p_supplierForest_actual_098304

def g32p_supplierForest_node_073059 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_073059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073059 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_150359 := by
  decide +kernel

theorem g32p_supplierForest_actual_073059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073059) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_073059
    g32p_supplierForest_actual_150359

def g32p_supplierForest_node_073104 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073104 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073104 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_017321 := by
  decide +kernel

theorem g32p_supplierForest_actual_073104 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073104) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 1 g32p_supplierForest_edge_073104
    g32p_supplierForest_actual_017321

def g32p_supplierForest_node_073165 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073165 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073165 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083291 := by
  decide +kernel

theorem g32p_supplierForest_actual_073165 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073165) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_073165
    g32p_supplierForest_actual_083291

def g32p_supplierForest_node_073187 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073187 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076490 := by
  decide +kernel

theorem g32p_supplierForest_actual_073187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073187) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_073187
    g32p_supplierForest_actual_076490

def g32p_supplierForest_node_073257 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_073257 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073257 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083253 := by
  decide +kernel

theorem g32p_supplierForest_actual_073257 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073257) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_073257
    g32p_supplierForest_actual_083253

def g32p_supplierForest_node_073319 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073319 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014766 := by
  decide +kernel

theorem g32p_supplierForest_actual_073319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073319) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_073319
    g32p_supplierForest_actual_014766

def g32p_supplierForest_node_073361 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073361 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073361 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_145523 := by
  decide +kernel

theorem g32p_supplierForest_actual_073361 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073361) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_073361
    g32p_supplierForest_actual_145523

def g32p_supplierForest_node_073400 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073400 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073400 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_013894 := by
  decide +kernel

theorem g32p_supplierForest_actual_073400 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073400) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_073400
    g32p_supplierForest_actual_013894

def g32p_supplierForest_node_073432 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073432 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073432 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_085663 := by
  decide +kernel

theorem g32p_supplierForest_actual_073432 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073432) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_073432
    g32p_supplierForest_actual_085663

def g32p_supplierForest_node_073439 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073439 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081046 := by
  decide +kernel

theorem g32p_supplierForest_actual_073439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073439) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_073439
    g32p_supplierForest_actual_081046

def g32p_supplierForest_node_073485 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073485 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073485 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_097957 := by
  decide +kernel

theorem g32p_supplierForest_actual_073485 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073485) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_073485
    g32p_supplierForest_actual_097957

def g32p_supplierForest_node_073511 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_073511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073511 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083246 := by
  decide +kernel

theorem g32p_supplierForest_actual_073511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073511) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_073511
    g32p_supplierForest_actual_083246

end HodgeLean.Foundations.Program

end
end
