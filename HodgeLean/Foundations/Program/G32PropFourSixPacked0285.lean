import HodgeLean.Foundations.Program.G32PropFourSixPacked0281
import HodgeLean.Foundations.Program.G32PropFourSixPacked0282
import HodgeLean.Foundations.Program.G32PropFourSixPacked0283
import HodgeLean.Foundations.Program.G32PropFourSixPacked0284
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0272
import HodgeLean.Foundations.Program.G32PropFourSixPacked0273
import HodgeLean.Foundations.Program.G32PropFourSixPacked0274
import HodgeLean.Foundations.Program.G32PropFourSixPacked0275
import HodgeLean.Foundations.Program.G32PropFourSixPacked0276
import HodgeLean.Foundations.Program.G32PropFourSixPacked0277
import HodgeLean.Foundations.Program.G32PropFourSixPacked0278

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_128 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_125741 else g32p_supplierForest_node_125761) else (if i.val < 3 then g32p_supplierForest_node_125794 else g32p_supplierForest_node_125803)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_125804 else g32p_supplierForest_node_125838) else (if i.val < 7 then g32p_supplierForest_node_125850 else g32p_supplierForest_node_125882))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_125902 else g32p_supplierForest_node_125915) else (if i.val < 11 then g32p_supplierForest_node_125964 else g32p_supplierForest_node_125990)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_126058 else g32p_supplierForest_node_126065) else (if i.val < 15 then g32p_supplierForest_node_126067 else g32p_supplierForest_node_126123)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_126147 else g32p_supplierForest_node_126161) else (if i.val < 19 then g32p_supplierForest_node_126213 else g32p_supplierForest_node_126236)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_126271 else g32p_supplierForest_node_126274) else (if i.val < 23 then g32p_supplierForest_node_126310 else g32p_supplierForest_node_126324))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_126358 else g32p_supplierForest_node_126433) else (if i.val < 27 then g32p_supplierForest_node_126447 else g32p_supplierForest_node_126489)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_126502 else g32p_supplierForest_node_126508) else (if i.val < 31 then g32p_supplierForest_node_126513 else g32p_supplierForest_node_126546))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_126567 else g32p_supplierForest_node_126678) else (if i.val < 35 then g32p_supplierForest_node_126817 else g32p_supplierForest_node_126820)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_126829 else g32p_supplierForest_node_126835) else (if i.val < 39 then g32p_supplierForest_node_126842 else g32p_supplierForest_node_126855))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_126885 else g32p_supplierForest_node_126887) else (if i.val < 43 then g32p_supplierForest_node_126905 else g32p_supplierForest_node_126909)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_126912 else g32p_supplierForest_node_126933) else (if i.val < 47 then g32p_supplierForest_node_126950 else g32p_supplierForest_node_127038)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_127114 else g32p_supplierForest_node_127179) else (if i.val < 51 then g32p_supplierForest_node_127180 else g32p_supplierForest_node_127277)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_127278 else g32p_supplierForest_node_127283) else (if i.val < 55 then g32p_supplierForest_node_127291 else g32p_supplierForest_node_127309))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_127342 else g32p_supplierForest_node_127356) else (if i.val < 59 then g32p_supplierForest_node_127364 else g32p_supplierForest_node_127372)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_127435 else g32p_supplierForest_node_127463) else (if i.val < 63 then g32p_supplierForest_node_127474 else g32p_supplierForest_node_127482)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_127485 else g32p_supplierForest_node_127518) else (if i.val < 67 then g32p_supplierForest_node_127628 else g32p_supplierForest_node_127631)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_127634 else g32p_supplierForest_node_127641) else (if i.val < 71 then g32p_supplierForest_node_127647 else g32p_supplierForest_node_127665))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_127679 else g32p_supplierForest_node_127819) else (if i.val < 75 then g32p_supplierForest_node_127836 else g32p_supplierForest_node_127908)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_127915 else g32p_supplierForest_node_127955) else (if i.val < 79 then g32p_supplierForest_node_127998 else g32p_supplierForest_node_128007)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_128016 else g32p_supplierForest_node_128029) else (if i.val < 83 then g32p_supplierForest_node_128037 else g32p_supplierForest_node_128042)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_128114 else g32p_supplierForest_node_128139) else (if i.val < 87 then g32p_supplierForest_node_128149 else g32p_supplierForest_node_128160))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_128170 else g32p_supplierForest_node_128198) else (if i.val < 91 then g32p_supplierForest_node_128199 else g32p_supplierForest_node_128228)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_128256 else g32p_supplierForest_node_128272) else (if i.val < 95 then g32p_supplierForest_node_128287 else g32p_supplierForest_node_128332))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_128338 else g32p_supplierForest_node_128347) else (if i.val < 99 then g32p_supplierForest_node_128393 else g32p_supplierForest_node_128412)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_128474 else g32p_supplierForest_node_128602) else (if i.val < 103 then g32p_supplierForest_node_128724 else g32p_supplierForest_node_128750))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_128754 else g32p_supplierForest_node_128758) else (if i.val < 107 then g32p_supplierForest_node_128777 else g32p_supplierForest_node_128798)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_128811 else g32p_supplierForest_node_128815) else (if i.val < 111 then g32p_supplierForest_node_128831 else g32p_supplierForest_node_128833)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_128914 else g32p_supplierForest_node_128926) else (if i.val < 115 then g32p_supplierForest_node_128957 else g32p_supplierForest_node_128969)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_128973 else g32p_supplierForest_node_129032) else (if i.val < 119 then g32p_supplierForest_node_129069 else g32p_supplierForest_node_129109))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_129209 else g32p_supplierForest_node_129251) else (if i.val < 123 then g32p_supplierForest_node_129270 else g32p_supplierForest_node_129344)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_129404 else g32p_supplierForest_node_129406) else (if i.val < 127 then g32p_supplierForest_node_129411 else g32p_supplierForest_node_129440))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_129509 else g32p_supplierForest_node_129552) else (if i.val < 131 then g32p_supplierForest_node_129554 else g32p_supplierForest_node_129561)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_129576 else g32p_supplierForest_node_129604) else (if i.val < 135 then g32p_supplierForest_node_129623 else g32p_supplierForest_node_129628))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_129633 else g32p_supplierForest_node_129647) else (if i.val < 139 then g32p_supplierForest_node_129657 else g32p_supplierForest_node_129674)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_129683 else g32p_supplierForest_node_129722) else (if i.val < 143 then g32p_supplierForest_node_129729 else g32p_supplierForest_node_129901)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_129923 else g32p_supplierForest_node_129926) else (if i.val < 147 then g32p_supplierForest_node_129943 else g32p_supplierForest_node_129962)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_129967 else g32p_supplierForest_node_129980) else (if i.val < 151 then g32p_supplierForest_node_130035 else g32p_supplierForest_node_130062))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_130075 else g32p_supplierForest_node_130076) else (if i.val < 155 then g32p_supplierForest_node_130127 else g32p_supplierForest_node_130195)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_130203 else g32p_supplierForest_node_130213) else (if i.val < 159 then g32p_supplierForest_node_130253 else g32p_supplierForest_node_130284))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_130301 else g32p_supplierForest_node_130313) else (if i.val < 163 then g32p_supplierForest_node_130323 else g32p_supplierForest_node_130340)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_130350 else g32p_supplierForest_node_130423) else (if i.val < 167 then g32p_supplierForest_node_130452 else g32p_supplierForest_node_130531))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_130565 else g32p_supplierForest_node_130582) else (if i.val < 171 then g32p_supplierForest_node_130625 else g32p_supplierForest_node_130689)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_130704 else g32p_supplierForest_node_130742) else (if i.val < 175 then g32p_supplierForest_node_130803 else g32p_supplierForest_node_130823)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_130870 else g32p_supplierForest_node_130879) else (if i.val < 179 then g32p_supplierForest_node_130892 else g32p_supplierForest_node_130896)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_130931 else g32p_supplierForest_node_130980) else (if i.val < 183 then g32p_supplierForest_node_131005 else g32p_supplierForest_node_131007))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_131058 else g32p_supplierForest_node_131098) else (if i.val < 187 then g32p_supplierForest_node_131101 else g32p_supplierForest_node_131107)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_131125 else g32p_supplierForest_node_131192) else (if i.val < 191 then g32p_supplierForest_node_131271 else g32p_supplierForest_node_131293)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_131294 else g32p_supplierForest_node_131334) else (if i.val < 195 then g32p_supplierForest_node_131348 else g32p_supplierForest_node_131357)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_131384 else g32p_supplierForest_node_131391) else (if i.val < 199 then g32p_supplierForest_node_131488 else g32p_supplierForest_node_131515))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_131612 else g32p_supplierForest_node_131613) else (if i.val < 203 then g32p_supplierForest_node_131631 else g32p_supplierForest_node_131645)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_131649 else g32p_supplierForest_node_131652) else (if i.val < 207 then g32p_supplierForest_node_131663 else g32p_supplierForest_node_131671)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_131679 else g32p_supplierForest_node_131694) else (if i.val < 211 then g32p_supplierForest_node_131731 else g32p_supplierForest_node_131743)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_131798 else g32p_supplierForest_node_131906) else (if i.val < 215 then g32p_supplierForest_node_131941 else g32p_supplierForest_node_131950))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_131971 else g32p_supplierForest_node_132012) else (if i.val < 219 then g32p_supplierForest_node_132017 else g32p_supplierForest_node_132026)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_132056 else g32p_supplierForest_node_132058) else (if i.val < 223 then g32p_supplierForest_node_132176 else g32p_supplierForest_node_132203))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_132307 else g32p_supplierForest_node_132352) else (if i.val < 227 then g32p_supplierForest_node_132361 else g32p_supplierForest_node_132384)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_132433 else g32p_supplierForest_node_132458) else (if i.val < 231 then g32p_supplierForest_node_132524 else g32p_supplierForest_node_132539))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_132546 else g32p_supplierForest_node_132551) else (if i.val < 235 then g32p_supplierForest_node_132566 else g32p_supplierForest_node_132587)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_132644 else g32p_supplierForest_node_132662) else (if i.val < 239 then g32p_supplierForest_node_132670 else g32p_supplierForest_node_132686)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_132712 else g32p_supplierForest_node_132725) else (if i.val < 243 then g32p_supplierForest_node_132800 else g32p_supplierForest_node_132883)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_132889 else g32p_supplierForest_node_132903) else (if i.val < 247 then g32p_supplierForest_node_132913 else g32p_supplierForest_node_132924))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_132958 else g32p_supplierForest_node_132993) else (if i.val < 251 then g32p_supplierForest_node_132999 else g32p_supplierForest_node_133097)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_133166 else g32p_supplierForest_node_133182) else (if i.val < 255 then g32p_supplierForest_node_133381 else g32p_supplierForest_node_133390))))))))

def g32p_supplierForest_classes_128 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 60 else 60) else (if i.val < 3 then 30 else 66)) else (if i.val < 6 then (if i.val < 5 then 62 else 60) else (if i.val < 7 then 60 else 57))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 36 else 57) else (if i.val < 11 then 60 else 62)) else (if i.val < 14 then (if i.val < 13 then 62 else 60) else (if i.val < 15 then 66 else 66)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 57 else 57) else (if i.val < 19 then 66 else 60)) else (if i.val < 22 then (if i.val < 21 then 59 else 60) else (if i.val < 23 then 60 else 58))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 66 else 29) else (if i.val < 27 then 57 else 33)) else (if i.val < 30 then (if i.val < 29 then 35 else 29) else (if i.val < 31 then 57 else 60))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 29 else 57) else (if i.val < 35 then 57 else 30)) else (if i.val < 38 then (if i.val < 37 then 60 else 30) else (if i.val < 39 then 35 else 57))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 60 else 36) else (if i.val < 43 then 30 else 30)) else (if i.val < 46 then (if i.val < 45 then 30 else 60) else (if i.val < 47 then 60 else 57)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 36 else 66) else (if i.val < 51 then 30 else 60)) else (if i.val < 54 then (if i.val < 53 then 36 else 30) else (if i.val < 55 then 30 else 61))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 35) else (if i.val < 59 then 60 else 57)) else (if i.val < 62 then (if i.val < 61 then 60 else 57) else (if i.val < 63 then 89 else 66)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 30 else 66) else (if i.val < 67 then 66 else 61)) else (if i.val < 70 then (if i.val < 69 then 61 else 57) else (if i.val < 71 then 30 else 57))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 30 else 38) else (if i.val < 75 then 21 else 21)) else (if i.val < 78 then (if i.val < 77 then 68 else 38) else (if i.val < 79 then 43 else 68)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 38) else (if i.val < 83 then 72 else 38)) else (if i.val < 86 then (if i.val < 85 then 73 else 21) else (if i.val < 87 then 38 else 73))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 38 else 40) else (if i.val < 91 then 21 else 21)) else (if i.val < 94 then (if i.val < 93 then 21 else 38) else (if i.val < 95 then 38 else 38))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 72 else 38) else (if i.val < 99 then 21 else 73)) else (if i.val < 102 then (if i.val < 101 then 38 else 38) else (if i.val < 103 then 38 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 7 else 42) else (if i.val < 107 then 38 else 21)) else (if i.val < 110 then (if i.val < 109 then 38 else 21) else (if i.val < 111 then 94 else 38)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 75 else 73) else (if i.val < 115 then 38 else 20)) else (if i.val < 118 then (if i.val < 117 then 38 else 20) else (if i.val < 119 then 38 else 38))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 38 else 40) else (if i.val < 123 then 38 else 38)) else (if i.val < 126 then (if i.val < 125 then 21 else 73) else (if i.val < 127 then 38 else 38))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 68 else 38) else (if i.val < 131 then 7 else 38)) else (if i.val < 134 then (if i.val < 133 then 73 else 72) else (if i.val < 135 then 21 else 21))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 38 else 72) else (if i.val < 139 then 38 else 74)) else (if i.val < 142 then (if i.val < 141 then 73 else 21) else (if i.val < 143 then 38 else 38)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 41 else 38) else (if i.val < 147 then 41 else 68)) else (if i.val < 150 then (if i.val < 149 then 38 else 70) else (if i.val < 151 then 21 else 20))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 20 else 74) else (if i.val < 155 then 38 else 21)) else (if i.val < 158 then (if i.val < 157 then 38 else 74) else (if i.val < 159 then 43 else 70))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 38 else 38) else (if i.val < 163 then 22 else 38)) else (if i.val < 166 then (if i.val < 165 then 21 else 38) else (if i.val < 167 then 38 else 73))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 73) else (if i.val < 171 then 38 else 38)) else (if i.val < 174 then (if i.val < 173 then 21 else 21) else (if i.val < 175 then 21 else 43)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 70 else 74) else (if i.val < 179 then 41 else 21)) else (if i.val < 182 then (if i.val < 181 then 38 else 42) else (if i.val < 183 then 38 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 21 else 38) else (if i.val < 187 then 74 else 38)) else (if i.val < 190 then (if i.val < 189 then 38 else 71) else (if i.val < 191 then 38 else 38)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 71 else 71) else (if i.val < 195 then 38 else 71)) else (if i.val < 198 then (if i.val < 197 then 38 else 42) else (if i.val < 199 then 68 else 21))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 73 else 21) else (if i.val < 203 then 40 else 38)) else (if i.val < 206 then (if i.val < 205 then 74 else 38) else (if i.val < 207 then 41 else 94)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 71 else 38) else (if i.val < 211 then 21 else 21)) else (if i.val < 214 then (if i.val < 213 then 38 else 71) else (if i.val < 215 then 21 else 21))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 73 else 40) else (if i.val < 219 then 68 else 21)) else (if i.val < 222 then (if i.val < 221 then 38 else 41) else (if i.val < 223 then 21 else 38))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 38 else 43) else (if i.val < 227 then 75 else 38)) else (if i.val < 230 then (if i.val < 229 then 73 else 73) else (if i.val < 231 then 38 else 38))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 38 else 73) else (if i.val < 235 then 43 else 71)) else (if i.val < 238 then (if i.val < 237 then 38 else 42) else (if i.val < 239 then 70 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 38 else 43) else (if i.val < 243 then 72 else 73)) else (if i.val < 246 then (if i.val < 245 then 38 else 21) else (if i.val < 247 then 21 else 40))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 43 else 43) else (if i.val < 251 then 21 else 38)) else (if i.val < 254 then (if i.val < 253 then 75 else 71) else (if i.val < 255 then 73 else 72))))))))

theorem g32p_supplierForest_actual_128 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_128 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_128 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_125741
  · exact g32p_supplierForest_actual_125761
  · exact g32p_supplierForest_actual_125794
  · exact g32p_supplierForest_actual_125803
  · exact g32p_supplierForest_actual_125804
  · exact g32p_supplierForest_actual_125838
  · exact g32p_supplierForest_actual_125850
  · exact g32p_supplierForest_actual_125882
  · exact g32p_supplierForest_actual_125902
  · exact g32p_supplierForest_actual_125915
  · exact g32p_supplierForest_actual_125964
  · exact g32p_supplierForest_actual_125990
  · exact g32p_supplierForest_actual_126058
  · exact g32p_supplierForest_actual_126065
  · exact g32p_supplierForest_actual_126067
  · exact g32p_supplierForest_actual_126123
  · exact g32p_supplierForest_actual_126147
  · exact g32p_supplierForest_actual_126161
  · exact g32p_supplierForest_actual_126213
  · exact g32p_supplierForest_actual_126236
  · exact g32p_supplierForest_actual_126271
  · exact g32p_supplierForest_actual_126274
  · exact g32p_supplierForest_actual_126310
  · exact g32p_supplierForest_actual_126324
  · exact g32p_supplierForest_actual_126358
  · exact g32p_supplierForest_actual_126433
  · exact g32p_supplierForest_actual_126447
  · exact g32p_supplierForest_actual_126489
  · exact g32p_supplierForest_actual_126502
  · exact g32p_supplierForest_actual_126508
  · exact g32p_supplierForest_actual_126513
  · exact g32p_supplierForest_actual_126546
  · exact g32p_supplierForest_actual_126567
  · exact g32p_supplierForest_actual_126678
  · exact g32p_supplierForest_actual_126817
  · exact g32p_supplierForest_actual_126820
  · exact g32p_supplierForest_actual_126829
  · exact g32p_supplierForest_actual_126835
  · exact g32p_supplierForest_actual_126842
  · exact g32p_supplierForest_actual_126855
  · exact g32p_supplierForest_actual_126885
  · exact g32p_supplierForest_actual_126887
  · exact g32p_supplierForest_actual_126905
  · exact g32p_supplierForest_actual_126909
  · exact g32p_supplierForest_actual_126912
  · exact g32p_supplierForest_actual_126933
  · exact g32p_supplierForest_actual_126950
  · exact g32p_supplierForest_actual_127038
  · exact g32p_supplierForest_actual_127114
  · exact g32p_supplierForest_actual_127179
  · exact g32p_supplierForest_actual_127180
  · exact g32p_supplierForest_actual_127277
  · exact g32p_supplierForest_actual_127278
  · exact g32p_supplierForest_actual_127283
  · exact g32p_supplierForest_actual_127291
  · exact g32p_supplierForest_actual_127309
  · exact g32p_supplierForest_actual_127342
  · exact g32p_supplierForest_actual_127356
  · exact g32p_supplierForest_actual_127364
  · exact g32p_supplierForest_actual_127372
  · exact g32p_supplierForest_actual_127435
  · exact g32p_supplierForest_actual_127463
  · exact g32p_supplierForest_actual_127474
  · exact g32p_supplierForest_actual_127482
  · exact g32p_supplierForest_actual_127485
  · exact g32p_supplierForest_actual_127518
  · exact g32p_supplierForest_actual_127628
  · exact g32p_supplierForest_actual_127631
  · exact g32p_supplierForest_actual_127634
  · exact g32p_supplierForest_actual_127641
  · exact g32p_supplierForest_actual_127647
  · exact g32p_supplierForest_actual_127665
  · exact g32p_supplierForest_actual_127679
  · exact g32p_supplierForest_actual_127819
  · exact g32p_supplierForest_actual_127836
  · exact g32p_supplierForest_actual_127908
  · exact g32p_supplierForest_actual_127915
  · exact g32p_supplierForest_actual_127955
  · exact g32p_supplierForest_actual_127998
  · exact g32p_supplierForest_actual_128007
  · exact g32p_supplierForest_actual_128016
  · exact g32p_supplierForest_actual_128029
  · exact g32p_supplierForest_actual_128037
  · exact g32p_supplierForest_actual_128042
  · exact g32p_supplierForest_actual_128114
  · exact g32p_supplierForest_actual_128139
  · exact g32p_supplierForest_actual_128149
  · exact g32p_supplierForest_actual_128160
  · exact g32p_supplierForest_actual_128170
  · exact g32p_supplierForest_actual_128198
  · exact g32p_supplierForest_actual_128199
  · exact g32p_supplierForest_actual_128228
  · exact g32p_supplierForest_actual_128256
  · exact g32p_supplierForest_actual_128272
  · exact g32p_supplierForest_actual_128287
  · exact g32p_supplierForest_actual_128332
  · exact g32p_supplierForest_actual_128338
  · exact g32p_supplierForest_actual_128347
  · exact g32p_supplierForest_actual_128393
  · exact g32p_supplierForest_actual_128412
  · exact g32p_supplierForest_actual_128474
  · exact g32p_supplierForest_actual_128602
  · exact g32p_supplierForest_actual_128724
  · exact g32p_supplierForest_actual_128750
  · exact g32p_supplierForest_actual_128754
  · exact g32p_supplierForest_actual_128758
  · exact g32p_supplierForest_actual_128777
  · exact g32p_supplierForest_actual_128798
  · exact g32p_supplierForest_actual_128811
  · exact g32p_supplierForest_actual_128815
  · exact g32p_supplierForest_actual_128831
  · exact g32p_supplierForest_actual_128833
  · exact g32p_supplierForest_actual_128914
  · exact g32p_supplierForest_actual_128926
  · exact g32p_supplierForest_actual_128957
  · exact g32p_supplierForest_actual_128969
  · exact g32p_supplierForest_actual_128973
  · exact g32p_supplierForest_actual_129032
  · exact g32p_supplierForest_actual_129069
  · exact g32p_supplierForest_actual_129109
  · exact g32p_supplierForest_actual_129209
  · exact g32p_supplierForest_actual_129251
  · exact g32p_supplierForest_actual_129270
  · exact g32p_supplierForest_actual_129344
  · exact g32p_supplierForest_actual_129404
  · exact g32p_supplierForest_actual_129406
  · exact g32p_supplierForest_actual_129411
  · exact g32p_supplierForest_actual_129440
  · exact g32p_supplierForest_actual_129509
  · exact g32p_supplierForest_actual_129552
  · exact g32p_supplierForest_actual_129554
  · exact g32p_supplierForest_actual_129561
  · exact g32p_supplierForest_actual_129576
  · exact g32p_supplierForest_actual_129604
  · exact g32p_supplierForest_actual_129623
  · exact g32p_supplierForest_actual_129628
  · exact g32p_supplierForest_actual_129633
  · exact g32p_supplierForest_actual_129647
  · exact g32p_supplierForest_actual_129657
  · exact g32p_supplierForest_actual_129674
  · exact g32p_supplierForest_actual_129683
  · exact g32p_supplierForest_actual_129722
  · exact g32p_supplierForest_actual_129729
  · exact g32p_supplierForest_actual_129901
  · exact g32p_supplierForest_actual_129923
  · exact g32p_supplierForest_actual_129926
  · exact g32p_supplierForest_actual_129943
  · exact g32p_supplierForest_actual_129962
  · exact g32p_supplierForest_actual_129967
  · exact g32p_supplierForest_actual_129980
  · exact g32p_supplierForest_actual_130035
  · exact g32p_supplierForest_actual_130062
  · exact g32p_supplierForest_actual_130075
  · exact g32p_supplierForest_actual_130076
  · exact g32p_supplierForest_actual_130127
  · exact g32p_supplierForest_actual_130195
  · exact g32p_supplierForest_actual_130203
  · exact g32p_supplierForest_actual_130213
  · exact g32p_supplierForest_actual_130253
  · exact g32p_supplierForest_actual_130284
  · exact g32p_supplierForest_actual_130301
  · exact g32p_supplierForest_actual_130313
  · exact g32p_supplierForest_actual_130323
  · exact g32p_supplierForest_actual_130340
  · exact g32p_supplierForest_actual_130350
  · exact g32p_supplierForest_actual_130423
  · exact g32p_supplierForest_actual_130452
  · exact g32p_supplierForest_actual_130531
  · exact g32p_supplierForest_actual_130565
  · exact g32p_supplierForest_actual_130582
  · exact g32p_supplierForest_actual_130625
  · exact g32p_supplierForest_actual_130689
  · exact g32p_supplierForest_actual_130704
  · exact g32p_supplierForest_actual_130742
  · exact g32p_supplierForest_actual_130803
  · exact g32p_supplierForest_actual_130823
  · exact g32p_supplierForest_actual_130870
  · exact g32p_supplierForest_actual_130879
  · exact g32p_supplierForest_actual_130892
  · exact g32p_supplierForest_actual_130896
  · exact g32p_supplierForest_actual_130931
  · exact g32p_supplierForest_actual_130980
  · exact g32p_supplierForest_actual_131005
  · exact g32p_supplierForest_actual_131007
  · exact g32p_supplierForest_actual_131058
  · exact g32p_supplierForest_actual_131098
  · exact g32p_supplierForest_actual_131101
  · exact g32p_supplierForest_actual_131107
  · exact g32p_supplierForest_actual_131125
  · exact g32p_supplierForest_actual_131192
  · exact g32p_supplierForest_actual_131271
  · exact g32p_supplierForest_actual_131293
  · exact g32p_supplierForest_actual_131294
  · exact g32p_supplierForest_actual_131334
  · exact g32p_supplierForest_actual_131348
  · exact g32p_supplierForest_actual_131357
  · exact g32p_supplierForest_actual_131384
  · exact g32p_supplierForest_actual_131391
  · exact g32p_supplierForest_actual_131488
  · exact g32p_supplierForest_actual_131515
  · exact g32p_supplierForest_actual_131612
  · exact g32p_supplierForest_actual_131613
  · exact g32p_supplierForest_actual_131631
  · exact g32p_supplierForest_actual_131645
  · exact g32p_supplierForest_actual_131649
  · exact g32p_supplierForest_actual_131652
  · exact g32p_supplierForest_actual_131663
  · exact g32p_supplierForest_actual_131671
  · exact g32p_supplierForest_actual_131679
  · exact g32p_supplierForest_actual_131694
  · exact g32p_supplierForest_actual_131731
  · exact g32p_supplierForest_actual_131743
  · exact g32p_supplierForest_actual_131798
  · exact g32p_supplierForest_actual_131906
  · exact g32p_supplierForest_actual_131941
  · exact g32p_supplierForest_actual_131950
  · exact g32p_supplierForest_actual_131971
  · exact g32p_supplierForest_actual_132012
  · exact g32p_supplierForest_actual_132017
  · exact g32p_supplierForest_actual_132026
  · exact g32p_supplierForest_actual_132056
  · exact g32p_supplierForest_actual_132058
  · exact g32p_supplierForest_actual_132176
  · exact g32p_supplierForest_actual_132203
  · exact g32p_supplierForest_actual_132307
  · exact g32p_supplierForest_actual_132352
  · exact g32p_supplierForest_actual_132361
  · exact g32p_supplierForest_actual_132384
  · exact g32p_supplierForest_actual_132433
  · exact g32p_supplierForest_actual_132458
  · exact g32p_supplierForest_actual_132524
  · exact g32p_supplierForest_actual_132539
  · exact g32p_supplierForest_actual_132546
  · exact g32p_supplierForest_actual_132551
  · exact g32p_supplierForest_actual_132566
  · exact g32p_supplierForest_actual_132587
  · exact g32p_supplierForest_actual_132644
  · exact g32p_supplierForest_actual_132662
  · exact g32p_supplierForest_actual_132670
  · exact g32p_supplierForest_actual_132686
  · exact g32p_supplierForest_actual_132712
  · exact g32p_supplierForest_actual_132725
  · exact g32p_supplierForest_actual_132800
  · exact g32p_supplierForest_actual_132883
  · exact g32p_supplierForest_actual_132889
  · exact g32p_supplierForest_actual_132903
  · exact g32p_supplierForest_actual_132913
  · exact g32p_supplierForest_actual_132924
  · exact g32p_supplierForest_actual_132958
  · exact g32p_supplierForest_actual_132993
  · exact g32p_supplierForest_actual_132999
  · exact g32p_supplierForest_actual_133097
  · exact g32p_supplierForest_actual_133166
  · exact g32p_supplierForest_actual_133182
  · exact g32p_supplierForest_actual_133381
  · exact g32p_supplierForest_actual_133390

def g32p_supplierForest_nodes_129 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_133399 else g32p_supplierForest_node_133408) else (if i.val < 3 then g32p_supplierForest_node_133414 else g32p_supplierForest_node_133420)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_133427 else g32p_supplierForest_node_133504) else (if i.val < 7 then g32p_supplierForest_node_133505 else g32p_supplierForest_node_133516))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_133524 else g32p_supplierForest_node_133546) else (if i.val < 11 then g32p_supplierForest_node_133579 else g32p_supplierForest_node_133670)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_133683 else g32p_supplierForest_node_133746) else (if i.val < 15 then g32p_supplierForest_node_133808 else g32p_supplierForest_node_133817)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_133842 else g32p_supplierForest_node_133844) else (if i.val < 19 then g32p_supplierForest_node_133884 else g32p_supplierForest_node_133886)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_133906 else g32p_supplierForest_node_133935) else (if i.val < 23 then g32p_supplierForest_node_133999 else g32p_supplierForest_node_134106))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_134108 else g32p_supplierForest_node_134184) else (if i.val < 27 then g32p_supplierForest_node_134217 else g32p_supplierForest_node_134219)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_134228 else g32p_supplierForest_node_134294) else (if i.val < 31 then g32p_supplierForest_node_134304 else g32p_supplierForest_node_134307))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_134337 else g32p_supplierForest_node_134343) else (if i.val < 35 then g32p_supplierForest_node_134367 else g32p_supplierForest_node_134379)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_134389 else g32p_supplierForest_node_134427) else (if i.val < 39 then g32p_supplierForest_node_134428 else g32p_supplierForest_node_134546))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_134547 else g32p_supplierForest_node_134590) else (if i.val < 43 then g32p_supplierForest_node_134638 else g32p_supplierForest_node_134667)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_134674 else g32p_supplierForest_node_134702) else (if i.val < 47 then g32p_supplierForest_node_134759 else g32p_supplierForest_node_134817)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_134834 else g32p_supplierForest_node_134856) else (if i.val < 51 then g32p_supplierForest_node_134897 else g32p_supplierForest_node_134914)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_134926 else g32p_supplierForest_node_134952) else (if i.val < 55 then g32p_supplierForest_node_134964 else g32p_supplierForest_node_134966))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_135049 else g32p_supplierForest_node_135054) else (if i.val < 59 then g32p_supplierForest_node_135064 else g32p_supplierForest_node_135073)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_135125 else g32p_supplierForest_node_135135) else (if i.val < 63 then g32p_supplierForest_node_135137 else g32p_supplierForest_node_135139)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_135158 else g32p_supplierForest_node_135213) else (if i.val < 67 then g32p_supplierForest_node_135272 else g32p_supplierForest_node_135328)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_135344 else g32p_supplierForest_node_135347) else (if i.val < 71 then g32p_supplierForest_node_135486 else g32p_supplierForest_node_135495))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_135499 else g32p_supplierForest_node_135627) else (if i.val < 75 then g32p_supplierForest_node_135634 else g32p_supplierForest_node_135669)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_135694 else g32p_supplierForest_node_135704) else (if i.val < 79 then g32p_supplierForest_node_135719 else g32p_supplierForest_node_135720)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_135759 else g32p_supplierForest_node_135764) else (if i.val < 83 then g32p_supplierForest_node_135781 else g32p_supplierForest_node_135808)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_135834 else g32p_supplierForest_node_136032) else (if i.val < 87 then g32p_supplierForest_node_136036 else g32p_supplierForest_node_136070))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_136086 else g32p_supplierForest_node_136121) else (if i.val < 91 then g32p_supplierForest_node_136133 else g32p_supplierForest_node_136214)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_136230 else g32p_supplierForest_node_136298) else (if i.val < 95 then g32p_supplierForest_node_136301 else g32p_supplierForest_node_136315))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_136337 else g32p_supplierForest_node_136338) else (if i.val < 99 then g32p_supplierForest_node_136375 else g32p_supplierForest_node_136405)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_136438 else g32p_supplierForest_node_136458) else (if i.val < 103 then g32p_supplierForest_node_136501 else g32p_supplierForest_node_136517))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_136568 else g32p_supplierForest_node_136569) else (if i.val < 107 then g32p_supplierForest_node_136572 else g32p_supplierForest_node_136589)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_136596 else g32p_supplierForest_node_136639) else (if i.val < 111 then g32p_supplierForest_node_136662 else g32p_supplierForest_node_136692)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_136771 else g32p_supplierForest_node_136775) else (if i.val < 115 then g32p_supplierForest_node_136804 else g32p_supplierForest_node_136816)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_136855 else g32p_supplierForest_node_136870) else (if i.val < 119 then g32p_supplierForest_node_136916 else g32p_supplierForest_node_136930))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_136977 else g32p_supplierForest_node_137016) else (if i.val < 123 then g32p_supplierForest_node_137027 else g32p_supplierForest_node_137075)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_137114 else g32p_supplierForest_node_137140) else (if i.val < 127 then g32p_supplierForest_node_137155 else g32p_supplierForest_node_137158))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_137173 else g32p_supplierForest_node_137233) else (if i.val < 131 then g32p_supplierForest_node_137355 else g32p_supplierForest_node_137439)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_137450 else g32p_supplierForest_node_137492) else (if i.val < 135 then g32p_supplierForest_node_137505 else g32p_supplierForest_node_137558))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_137565 else g32p_supplierForest_node_137587) else (if i.val < 139 then g32p_supplierForest_node_137612 else g32p_supplierForest_node_137615)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_137636 else g32p_supplierForest_node_137664) else (if i.val < 143 then g32p_supplierForest_node_137724 else g32p_supplierForest_node_137761)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_137786 else g32p_supplierForest_node_137839) else (if i.val < 147 then g32p_supplierForest_node_137843 else g32p_supplierForest_node_137875)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_137919 else g32p_supplierForest_node_138022) else (if i.val < 151 then g32p_supplierForest_node_138034 else g32p_supplierForest_node_138063))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_138067 else g32p_supplierForest_node_138095) else (if i.val < 155 then g32p_supplierForest_node_138156 else g32p_supplierForest_node_138185)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_138278 else g32p_supplierForest_node_138303) else (if i.val < 159 then g32p_supplierForest_node_138337 else g32p_supplierForest_node_138338))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_138341 else g32p_supplierForest_node_138409) else (if i.val < 163 then g32p_supplierForest_node_138430 else g32p_supplierForest_node_138438)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_138455 else g32p_supplierForest_node_138471) else (if i.val < 167 then g32p_supplierForest_node_138500 else g32p_supplierForest_node_138504))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_138511 else g32p_supplierForest_node_138543) else (if i.val < 171 then g32p_supplierForest_node_138598 else g32p_supplierForest_node_138616)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_138627 else g32p_supplierForest_node_138707) else (if i.val < 175 then g32p_supplierForest_node_138798 else g32p_supplierForest_node_138817)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_138824 else g32p_supplierForest_node_138856) else (if i.val < 179 then g32p_supplierForest_node_139065 else g32p_supplierForest_node_139082)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_139117 else g32p_supplierForest_node_139170) else (if i.val < 183 then g32p_supplierForest_node_139179 else g32p_supplierForest_node_139198))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_139207 else g32p_supplierForest_node_139237) else (if i.val < 187 then g32p_supplierForest_node_139251 else g32p_supplierForest_node_139332)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_139357 else g32p_supplierForest_node_139362) else (if i.val < 191 then g32p_supplierForest_node_139363 else g32p_supplierForest_node_139378)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_139383 else g32p_supplierForest_node_139388) else (if i.val < 195 then g32p_supplierForest_node_139394 else g32p_supplierForest_node_139415)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_139419 else g32p_supplierForest_node_139433) else (if i.val < 199 then g32p_supplierForest_node_139444 else g32p_supplierForest_node_139467))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_139685 else g32p_supplierForest_node_139709) else (if i.val < 203 then g32p_supplierForest_node_139722 else g32p_supplierForest_node_139733)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_139768 else g32p_supplierForest_node_139805) else (if i.val < 207 then g32p_supplierForest_node_139813 else g32p_supplierForest_node_139815)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_139831 else g32p_supplierForest_node_139837) else (if i.val < 211 then g32p_supplierForest_node_139841 else g32p_supplierForest_node_139855)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_139860 else g32p_supplierForest_node_139883) else (if i.val < 215 then g32p_supplierForest_node_139900 else g32p_supplierForest_node_139951))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_139961 else g32p_supplierForest_node_139962) else (if i.val < 219 then g32p_supplierForest_node_139977 else g32p_supplierForest_node_140064)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_140135 else g32p_supplierForest_node_140177) else (if i.val < 223 then g32p_supplierForest_node_140197 else g32p_supplierForest_node_140320))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_140413 else g32p_supplierForest_node_140426) else (if i.val < 227 then g32p_supplierForest_node_140446 else g32p_supplierForest_node_140491)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_140517 else g32p_supplierForest_node_140526) else (if i.val < 231 then g32p_supplierForest_node_140536 else g32p_supplierForest_node_140564))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_140594 else g32p_supplierForest_node_140654) else (if i.val < 235 then g32p_supplierForest_node_140669 else g32p_supplierForest_node_140762)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_140767 else g32p_supplierForest_node_140786) else (if i.val < 239 then g32p_supplierForest_node_140810 else g32p_supplierForest_node_140831)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_140888 else g32p_supplierForest_node_140946) else (if i.val < 243 then g32p_supplierForest_node_140950 else g32p_supplierForest_node_140965)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_141077 else g32p_supplierForest_node_141093) else (if i.val < 247 then g32p_supplierForest_node_141120 else g32p_supplierForest_node_141213))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_141222 else g32p_supplierForest_node_141317) else (if i.val < 251 then g32p_supplierForest_node_141355 else g32p_supplierForest_node_141374)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_141398 else g32p_supplierForest_node_141420) else (if i.val < 255 then g32p_supplierForest_node_141421 else g32p_supplierForest_node_141458))))))))

def g32p_supplierForest_classes_129 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 71 else 21) else (if i.val < 3 then 72 else 72)) else (if i.val < 6 then (if i.val < 5 then 21 else 73) else (if i.val < 7 then 38 else 38))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 22 else 68) else (if i.val < 11 then 68 else 73)) else (if i.val < 14 then (if i.val < 13 then 73 else 71) else (if i.val < 15 then 71 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 71 else 21) else (if i.val < 19 then 22 else 74)) else (if i.val < 22 then (if i.val < 21 then 73 else 71) else (if i.val < 23 then 38 else 21))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 42 else 73) else (if i.val < 27 then 21 else 38)) else (if i.val < 30 then (if i.val < 29 then 73 else 38) else (if i.val < 31 then 21 else 21))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 71 else 73) else (if i.val < 35 then 21 else 38)) else (if i.val < 38 then (if i.val < 37 then 68 else 38) else (if i.val < 39 then 41 else 38))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 70) else (if i.val < 43 then 42 else 38)) else (if i.val < 46 then (if i.val < 45 then 38 else 38) else (if i.val < 47 then 70 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 21 else 38) else (if i.val < 51 then 73 else 21)) else (if i.val < 54 then (if i.val < 53 then 38 else 68) else (if i.val < 55 then 94 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 73 else 38) else (if i.val < 59 then 38 else 20)) else (if i.val < 62 then (if i.val < 61 then 20 else 38) else (if i.val < 63 then 38 else 21)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 38 else 74) else (if i.val < 67 then 21 else 20)) else (if i.val < 70 then (if i.val < 69 then 73 else 71) else (if i.val < 71 then 21 else 68))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 73 else 38) else (if i.val < 75 then 21 else 7)) else (if i.val < 78 then (if i.val < 77 then 21 else 42) else (if i.val < 79 then 41 else 43)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 71 else 21) else (if i.val < 83 then 73 else 38)) else (if i.val < 86 then (if i.val < 85 then 38 else 71) else (if i.val < 87 then 21 else 38))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 20 else 70) else (if i.val < 91 then 21 else 73)) else (if i.val < 94 then (if i.val < 93 then 38 else 73) else (if i.val < 95 then 42 else 38))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 68 else 68) else (if i.val < 99 then 38 else 21)) else (if i.val < 102 then (if i.val < 101 then 21 else 43) else (if i.val < 103 then 38 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 41 else 38) else (if i.val < 107 then 21 else 73)) else (if i.val < 110 then (if i.val < 109 then 40 else 73) else (if i.val < 111 then 73 else 40)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 73 else 73) else (if i.val < 115 then 38 else 72)) else (if i.val < 118 then (if i.val < 117 then 42 else 71) else (if i.val < 119 then 79 else 22))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 38 else 74) else (if i.val < 123 then 38 else 40)) else (if i.val < 126 then (if i.val < 125 then 73 else 73) else (if i.val < 127 then 73 else 38))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 43 else 71) else (if i.val < 131 then 38 else 71)) else (if i.val < 134 then (if i.val < 133 then 41 else 21) else (if i.val < 135 then 21 else 43))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 21 else 21) else (if i.val < 139 then 73 else 73)) else (if i.val < 142 then (if i.val < 141 then 38 else 73) else (if i.val < 143 then 38 else 43)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 73 else 38) else (if i.val < 147 then 38 else 21)) else (if i.val < 150 then (if i.val < 149 then 94 else 68) else (if i.val < 151 then 38 else 73))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 21 else 70) else (if i.val < 155 then 70 else 38)) else (if i.val < 158 then (if i.val < 157 then 73 else 73) else (if i.val < 159 then 38 else 68))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 38 else 21) else (if i.val < 163 then 21 else 21)) else (if i.val < 166 then (if i.val < 165 then 41 else 43) else (if i.val < 167 then 38 else 73))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 68) else (if i.val < 171 then 38 else 38)) else (if i.val < 174 then (if i.val < 173 then 38 else 73) else (if i.val < 175 then 38 else 75)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 73 else 74) else (if i.val < 179 then 72 else 38)) else (if i.val < 182 then (if i.val < 181 then 20 else 74) else (if i.val < 183 then 38 else 71))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 72 else 38) else (if i.val < 187 then 38 else 38)) else (if i.val < 190 then (if i.val < 189 then 41 else 73) else (if i.val < 191 then 68 else 7)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 73 else 42) else (if i.val < 195 then 38 else 73)) else (if i.val < 198 then (if i.val < 197 then 71 else 41) else (if i.val < 199 then 41 else 73))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 43 else 38) else (if i.val < 203 then 94 else 73)) else (if i.val < 206 then (if i.val < 205 then 74 else 73) else (if i.val < 207 then 41 else 38)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 38 else 21) else (if i.val < 211 then 72 else 71)) else (if i.val < 214 then (if i.val < 213 then 74 else 38) else (if i.val < 215 then 71 else 73))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 73 else 20) else (if i.val < 219 then 21 else 38)) else (if i.val < 222 then (if i.val < 221 then 71 else 41) else (if i.val < 223 then 73 else 73))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 21 else 73) else (if i.val < 227 then 38 else 21)) else (if i.val < 230 then (if i.val < 229 then 21 else 21) else (if i.val < 231 then 21 else 21))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 75 else 73) else (if i.val < 235 then 73 else 38)) else (if i.val < 238 then (if i.val < 237 then 40 else 42) else (if i.val < 239 then 73 else 38)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 74 else 73) else (if i.val < 243 then 21 else 38)) else (if i.val < 246 then (if i.val < 245 then 38 else 69) else (if i.val < 247 then 41 else 38))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 40 else 38) else (if i.val < 251 then 73 else 38)) else (if i.val < 254 then (if i.val < 253 then 38 else 73) else (if i.val < 255 then 21 else 38))))))))

theorem g32p_supplierForest_actual_129 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_129 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_129 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_133399
  · exact g32p_supplierForest_actual_133408
  · exact g32p_supplierForest_actual_133414
  · exact g32p_supplierForest_actual_133420
  · exact g32p_supplierForest_actual_133427
  · exact g32p_supplierForest_actual_133504
  · exact g32p_supplierForest_actual_133505
  · exact g32p_supplierForest_actual_133516
  · exact g32p_supplierForest_actual_133524
  · exact g32p_supplierForest_actual_133546
  · exact g32p_supplierForest_actual_133579
  · exact g32p_supplierForest_actual_133670
  · exact g32p_supplierForest_actual_133683
  · exact g32p_supplierForest_actual_133746
  · exact g32p_supplierForest_actual_133808
  · exact g32p_supplierForest_actual_133817
  · exact g32p_supplierForest_actual_133842
  · exact g32p_supplierForest_actual_133844
  · exact g32p_supplierForest_actual_133884
  · exact g32p_supplierForest_actual_133886
  · exact g32p_supplierForest_actual_133906
  · exact g32p_supplierForest_actual_133935
  · exact g32p_supplierForest_actual_133999
  · exact g32p_supplierForest_actual_134106
  · exact g32p_supplierForest_actual_134108
  · exact g32p_supplierForest_actual_134184
  · exact g32p_supplierForest_actual_134217
  · exact g32p_supplierForest_actual_134219
  · exact g32p_supplierForest_actual_134228
  · exact g32p_supplierForest_actual_134294
  · exact g32p_supplierForest_actual_134304
  · exact g32p_supplierForest_actual_134307
  · exact g32p_supplierForest_actual_134337
  · exact g32p_supplierForest_actual_134343
  · exact g32p_supplierForest_actual_134367
  · exact g32p_supplierForest_actual_134379
  · exact g32p_supplierForest_actual_134389
  · exact g32p_supplierForest_actual_134427
  · exact g32p_supplierForest_actual_134428
  · exact g32p_supplierForest_actual_134546
  · exact g32p_supplierForest_actual_134547
  · exact g32p_supplierForest_actual_134590
  · exact g32p_supplierForest_actual_134638
  · exact g32p_supplierForest_actual_134667
  · exact g32p_supplierForest_actual_134674
  · exact g32p_supplierForest_actual_134702
  · exact g32p_supplierForest_actual_134759
  · exact g32p_supplierForest_actual_134817
  · exact g32p_supplierForest_actual_134834
  · exact g32p_supplierForest_actual_134856
  · exact g32p_supplierForest_actual_134897
  · exact g32p_supplierForest_actual_134914
  · exact g32p_supplierForest_actual_134926
  · exact g32p_supplierForest_actual_134952
  · exact g32p_supplierForest_actual_134964
  · exact g32p_supplierForest_actual_134966
  · exact g32p_supplierForest_actual_135049
  · exact g32p_supplierForest_actual_135054
  · exact g32p_supplierForest_actual_135064
  · exact g32p_supplierForest_actual_135073
  · exact g32p_supplierForest_actual_135125
  · exact g32p_supplierForest_actual_135135
  · exact g32p_supplierForest_actual_135137
  · exact g32p_supplierForest_actual_135139
  · exact g32p_supplierForest_actual_135158
  · exact g32p_supplierForest_actual_135213
  · exact g32p_supplierForest_actual_135272
  · exact g32p_supplierForest_actual_135328
  · exact g32p_supplierForest_actual_135344
  · exact g32p_supplierForest_actual_135347
  · exact g32p_supplierForest_actual_135486
  · exact g32p_supplierForest_actual_135495
  · exact g32p_supplierForest_actual_135499
  · exact g32p_supplierForest_actual_135627
  · exact g32p_supplierForest_actual_135634
  · exact g32p_supplierForest_actual_135669
  · exact g32p_supplierForest_actual_135694
  · exact g32p_supplierForest_actual_135704
  · exact g32p_supplierForest_actual_135719
  · exact g32p_supplierForest_actual_135720
  · exact g32p_supplierForest_actual_135759
  · exact g32p_supplierForest_actual_135764
  · exact g32p_supplierForest_actual_135781
  · exact g32p_supplierForest_actual_135808
  · exact g32p_supplierForest_actual_135834
  · exact g32p_supplierForest_actual_136032
  · exact g32p_supplierForest_actual_136036
  · exact g32p_supplierForest_actual_136070
  · exact g32p_supplierForest_actual_136086
  · exact g32p_supplierForest_actual_136121
  · exact g32p_supplierForest_actual_136133
  · exact g32p_supplierForest_actual_136214
  · exact g32p_supplierForest_actual_136230
  · exact g32p_supplierForest_actual_136298
  · exact g32p_supplierForest_actual_136301
  · exact g32p_supplierForest_actual_136315
  · exact g32p_supplierForest_actual_136337
  · exact g32p_supplierForest_actual_136338
  · exact g32p_supplierForest_actual_136375
  · exact g32p_supplierForest_actual_136405
  · exact g32p_supplierForest_actual_136438
  · exact g32p_supplierForest_actual_136458
  · exact g32p_supplierForest_actual_136501
  · exact g32p_supplierForest_actual_136517
  · exact g32p_supplierForest_actual_136568
  · exact g32p_supplierForest_actual_136569
  · exact g32p_supplierForest_actual_136572
  · exact g32p_supplierForest_actual_136589
  · exact g32p_supplierForest_actual_136596
  · exact g32p_supplierForest_actual_136639
  · exact g32p_supplierForest_actual_136662
  · exact g32p_supplierForest_actual_136692
  · exact g32p_supplierForest_actual_136771
  · exact g32p_supplierForest_actual_136775
  · exact g32p_supplierForest_actual_136804
  · exact g32p_supplierForest_actual_136816
  · exact g32p_supplierForest_actual_136855
  · exact g32p_supplierForest_actual_136870
  · exact g32p_supplierForest_actual_136916
  · exact g32p_supplierForest_actual_136930
  · exact g32p_supplierForest_actual_136977
  · exact g32p_supplierForest_actual_137016
  · exact g32p_supplierForest_actual_137027
  · exact g32p_supplierForest_actual_137075
  · exact g32p_supplierForest_actual_137114
  · exact g32p_supplierForest_actual_137140
  · exact g32p_supplierForest_actual_137155
  · exact g32p_supplierForest_actual_137158
  · exact g32p_supplierForest_actual_137173
  · exact g32p_supplierForest_actual_137233
  · exact g32p_supplierForest_actual_137355
  · exact g32p_supplierForest_actual_137439
  · exact g32p_supplierForest_actual_137450
  · exact g32p_supplierForest_actual_137492
  · exact g32p_supplierForest_actual_137505
  · exact g32p_supplierForest_actual_137558
  · exact g32p_supplierForest_actual_137565
  · exact g32p_supplierForest_actual_137587
  · exact g32p_supplierForest_actual_137612
  · exact g32p_supplierForest_actual_137615
  · exact g32p_supplierForest_actual_137636
  · exact g32p_supplierForest_actual_137664
  · exact g32p_supplierForest_actual_137724
  · exact g32p_supplierForest_actual_137761
  · exact g32p_supplierForest_actual_137786
  · exact g32p_supplierForest_actual_137839
  · exact g32p_supplierForest_actual_137843
  · exact g32p_supplierForest_actual_137875
  · exact g32p_supplierForest_actual_137919
  · exact g32p_supplierForest_actual_138022
  · exact g32p_supplierForest_actual_138034
  · exact g32p_supplierForest_actual_138063
  · exact g32p_supplierForest_actual_138067
  · exact g32p_supplierForest_actual_138095
  · exact g32p_supplierForest_actual_138156
  · exact g32p_supplierForest_actual_138185
  · exact g32p_supplierForest_actual_138278
  · exact g32p_supplierForest_actual_138303
  · exact g32p_supplierForest_actual_138337
  · exact g32p_supplierForest_actual_138338
  · exact g32p_supplierForest_actual_138341
  · exact g32p_supplierForest_actual_138409
  · exact g32p_supplierForest_actual_138430
  · exact g32p_supplierForest_actual_138438
  · exact g32p_supplierForest_actual_138455
  · exact g32p_supplierForest_actual_138471
  · exact g32p_supplierForest_actual_138500
  · exact g32p_supplierForest_actual_138504
  · exact g32p_supplierForest_actual_138511
  · exact g32p_supplierForest_actual_138543
  · exact g32p_supplierForest_actual_138598
  · exact g32p_supplierForest_actual_138616
  · exact g32p_supplierForest_actual_138627
  · exact g32p_supplierForest_actual_138707
  · exact g32p_supplierForest_actual_138798
  · exact g32p_supplierForest_actual_138817
  · exact g32p_supplierForest_actual_138824
  · exact g32p_supplierForest_actual_138856
  · exact g32p_supplierForest_actual_139065
  · exact g32p_supplierForest_actual_139082
  · exact g32p_supplierForest_actual_139117
  · exact g32p_supplierForest_actual_139170
  · exact g32p_supplierForest_actual_139179
  · exact g32p_supplierForest_actual_139198
  · exact g32p_supplierForest_actual_139207
  · exact g32p_supplierForest_actual_139237
  · exact g32p_supplierForest_actual_139251
  · exact g32p_supplierForest_actual_139332
  · exact g32p_supplierForest_actual_139357
  · exact g32p_supplierForest_actual_139362
  · exact g32p_supplierForest_actual_139363
  · exact g32p_supplierForest_actual_139378
  · exact g32p_supplierForest_actual_139383
  · exact g32p_supplierForest_actual_139388
  · exact g32p_supplierForest_actual_139394
  · exact g32p_supplierForest_actual_139415
  · exact g32p_supplierForest_actual_139419
  · exact g32p_supplierForest_actual_139433
  · exact g32p_supplierForest_actual_139444
  · exact g32p_supplierForest_actual_139467
  · exact g32p_supplierForest_actual_139685
  · exact g32p_supplierForest_actual_139709
  · exact g32p_supplierForest_actual_139722
  · exact g32p_supplierForest_actual_139733
  · exact g32p_supplierForest_actual_139768
  · exact g32p_supplierForest_actual_139805
  · exact g32p_supplierForest_actual_139813
  · exact g32p_supplierForest_actual_139815
  · exact g32p_supplierForest_actual_139831
  · exact g32p_supplierForest_actual_139837
  · exact g32p_supplierForest_actual_139841
  · exact g32p_supplierForest_actual_139855
  · exact g32p_supplierForest_actual_139860
  · exact g32p_supplierForest_actual_139883
  · exact g32p_supplierForest_actual_139900
  · exact g32p_supplierForest_actual_139951
  · exact g32p_supplierForest_actual_139961
  · exact g32p_supplierForest_actual_139962
  · exact g32p_supplierForest_actual_139977
  · exact g32p_supplierForest_actual_140064
  · exact g32p_supplierForest_actual_140135
  · exact g32p_supplierForest_actual_140177
  · exact g32p_supplierForest_actual_140197
  · exact g32p_supplierForest_actual_140320
  · exact g32p_supplierForest_actual_140413
  · exact g32p_supplierForest_actual_140426
  · exact g32p_supplierForest_actual_140446
  · exact g32p_supplierForest_actual_140491
  · exact g32p_supplierForest_actual_140517
  · exact g32p_supplierForest_actual_140526
  · exact g32p_supplierForest_actual_140536
  · exact g32p_supplierForest_actual_140564
  · exact g32p_supplierForest_actual_140594
  · exact g32p_supplierForest_actual_140654
  · exact g32p_supplierForest_actual_140669
  · exact g32p_supplierForest_actual_140762
  · exact g32p_supplierForest_actual_140767
  · exact g32p_supplierForest_actual_140786
  · exact g32p_supplierForest_actual_140810
  · exact g32p_supplierForest_actual_140831
  · exact g32p_supplierForest_actual_140888
  · exact g32p_supplierForest_actual_140946
  · exact g32p_supplierForest_actual_140950
  · exact g32p_supplierForest_actual_140965
  · exact g32p_supplierForest_actual_141077
  · exact g32p_supplierForest_actual_141093
  · exact g32p_supplierForest_actual_141120
  · exact g32p_supplierForest_actual_141213
  · exact g32p_supplierForest_actual_141222
  · exact g32p_supplierForest_actual_141317
  · exact g32p_supplierForest_actual_141355
  · exact g32p_supplierForest_actual_141374
  · exact g32p_supplierForest_actual_141398
  · exact g32p_supplierForest_actual_141420
  · exact g32p_supplierForest_actual_141421
  · exact g32p_supplierForest_actual_141458

def g32p_supplierForest_nodes_130 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_141576 else g32p_supplierForest_node_141598) else (if i.val < 3 then g32p_supplierForest_node_141666 else g32p_supplierForest_node_141710)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_141741 else g32p_supplierForest_node_141747) else (if i.val < 7 then g32p_supplierForest_node_141862 else g32p_supplierForest_node_141869))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_141936 else g32p_supplierForest_node_141943) else (if i.val < 11 then g32p_supplierForest_node_141963 else g32p_supplierForest_node_141970)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_141975 else g32p_supplierForest_node_142000) else (if i.val < 15 then g32p_supplierForest_node_142005 else g32p_supplierForest_node_142020)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_142021 else g32p_supplierForest_node_142041) else (if i.val < 19 then g32p_supplierForest_node_142057 else g32p_supplierForest_node_142093)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_142165 else g32p_supplierForest_node_142224) else (if i.val < 23 then g32p_supplierForest_node_142246 else g32p_supplierForest_node_142288))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_142370 else g32p_supplierForest_node_142384) else (if i.val < 27 then g32p_supplierForest_node_142410 else g32p_supplierForest_node_142431)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_142454 else g32p_supplierForest_node_142455) else (if i.val < 31 then g32p_supplierForest_node_142479 else g32p_supplierForest_node_142491))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_142511 else g32p_supplierForest_node_142539) else (if i.val < 35 then g32p_supplierForest_node_142558 else g32p_supplierForest_node_142582)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_142607 else g32p_supplierForest_node_142611) else (if i.val < 39 then g32p_supplierForest_node_142622 else g32p_supplierForest_node_142659))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_142660 else g32p_supplierForest_node_142668) else (if i.val < 43 then g32p_supplierForest_node_142736 else g32p_supplierForest_node_142744)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_142748 else g32p_supplierForest_node_142761) else (if i.val < 47 then g32p_supplierForest_node_142780 else g32p_supplierForest_node_142796)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_142806 else g32p_supplierForest_node_142810) else (if i.val < 51 then g32p_supplierForest_node_142816 else g32p_supplierForest_node_142827)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_142925 else g32p_supplierForest_node_142927) else (if i.val < 55 then g32p_supplierForest_node_142971 else g32p_supplierForest_node_142984))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_143070 else g32p_supplierForest_node_143094) else (if i.val < 59 then g32p_supplierForest_node_143162 else g32p_supplierForest_node_143182)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_143193 else g32p_supplierForest_node_143206) else (if i.val < 63 then g32p_supplierForest_node_143211 else g32p_supplierForest_node_143263)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_143317 else g32p_supplierForest_node_143349) else (if i.val < 67 then g32p_supplierForest_node_143409 else g32p_supplierForest_node_143438)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_143456 else g32p_supplierForest_node_143457) else (if i.val < 71 then g32p_supplierForest_node_143462 else g32p_supplierForest_node_143473))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_143509 else g32p_supplierForest_node_143542) else (if i.val < 75 then g32p_supplierForest_node_143561 else g32p_supplierForest_node_143606)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_143631 else g32p_supplierForest_node_143683) else (if i.val < 79 then g32p_supplierForest_node_143700 else g32p_supplierForest_node_143737)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_143817 else g32p_supplierForest_node_143828) else (if i.val < 83 then g32p_supplierForest_node_143838 else g32p_supplierForest_node_143907)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_143921 else g32p_supplierForest_node_143940) else (if i.val < 87 then g32p_supplierForest_node_143982 else g32p_supplierForest_node_143990))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_143995 else g32p_supplierForest_node_144004) else (if i.val < 91 then g32p_supplierForest_node_144012 else g32p_supplierForest_node_144056)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_144075 else g32p_supplierForest_node_144092) else (if i.val < 95 then g32p_supplierForest_node_144093 else g32p_supplierForest_node_144104))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_144129 else g32p_supplierForest_node_144226) else (if i.val < 99 then g32p_supplierForest_node_144246 else g32p_supplierForest_node_144386)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_144406 else g32p_supplierForest_node_144464) else (if i.val < 103 then g32p_supplierForest_node_144643 else g32p_supplierForest_node_144710))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_144728 else g32p_supplierForest_node_144748) else (if i.val < 107 then g32p_supplierForest_node_144759 else g32p_supplierForest_node_144786)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_144794 else g32p_supplierForest_node_144834) else (if i.val < 111 then g32p_supplierForest_node_144877 else g32p_supplierForest_node_144894)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_145059 else g32p_supplierForest_node_145071) else (if i.val < 115 then g32p_supplierForest_node_145094 else g32p_supplierForest_node_145118)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_145140 else g32p_supplierForest_node_145141) else (if i.val < 119 then g32p_supplierForest_node_145188 else g32p_supplierForest_node_145190))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_145233 else g32p_supplierForest_node_145236) else (if i.val < 123 then g32p_supplierForest_node_145252 else g32p_supplierForest_node_145286)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_145314 else g32p_supplierForest_node_145335) else (if i.val < 127 then g32p_supplierForest_node_145393 else g32p_supplierForest_node_145454))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_145507 else g32p_supplierForest_node_145559) else (if i.val < 131 then g32p_supplierForest_node_145569 else g32p_supplierForest_node_145597)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_145624 else g32p_supplierForest_node_145637) else (if i.val < 135 then g32p_supplierForest_node_145707 else g32p_supplierForest_node_145745))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_145828 else g32p_supplierForest_node_145868) else (if i.val < 139 then g32p_supplierForest_node_145900 else g32p_supplierForest_node_145919)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_145929 else g32p_supplierForest_node_145940) else (if i.val < 143 then g32p_supplierForest_node_145965 else g32p_supplierForest_node_145984)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_146010 else g32p_supplierForest_node_146025) else (if i.val < 147 then g32p_supplierForest_node_146082 else g32p_supplierForest_node_146164)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_146184 else g32p_supplierForest_node_146194) else (if i.val < 151 then g32p_supplierForest_node_146288 else g32p_supplierForest_node_146317))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_146348 else g32p_supplierForest_node_146382) else (if i.val < 155 then g32p_supplierForest_node_146562 else g32p_supplierForest_node_146728)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_146768 else g32p_supplierForest_node_146770) else (if i.val < 159 then g32p_supplierForest_node_146777 else g32p_supplierForest_node_146786))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_146790 else g32p_supplierForest_node_146797) else (if i.val < 163 then g32p_supplierForest_node_146897 else g32p_supplierForest_node_146955)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_146983 else g32p_supplierForest_node_147002) else (if i.val < 167 then g32p_supplierForest_node_147107 else g32p_supplierForest_node_147147))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_147152 else g32p_supplierForest_node_147169) else (if i.val < 171 then g32p_supplierForest_node_147196 else g32p_supplierForest_node_147211)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_147235 else g32p_supplierForest_node_147239) else (if i.val < 175 then g32p_supplierForest_node_147282 else g32p_supplierForest_node_147324)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_147403 else g32p_supplierForest_node_147409) else (if i.val < 179 then g32p_supplierForest_node_147451 else g32p_supplierForest_node_147471)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_147577 else g32p_supplierForest_node_147602) else (if i.val < 183 then g32p_supplierForest_node_147611 else g32p_supplierForest_node_147619))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_147621 else g32p_supplierForest_node_147629) else (if i.val < 187 then g32p_supplierForest_node_147667 else g32p_supplierForest_node_147680)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_147794 else g32p_supplierForest_node_147796) else (if i.val < 191 then g32p_supplierForest_node_147800 else g32p_supplierForest_node_147810)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_147871 else g32p_supplierForest_node_147930) else (if i.val < 195 then g32p_supplierForest_node_147956 else g32p_supplierForest_node_147990)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_147998 else g32p_supplierForest_node_148035) else (if i.val < 199 then g32p_supplierForest_node_148075 else g32p_supplierForest_node_148079))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_148132 else g32p_supplierForest_node_148233) else (if i.val < 203 then g32p_supplierForest_node_148272 else g32p_supplierForest_node_148312)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_148325 else g32p_supplierForest_node_148346) else (if i.val < 207 then g32p_supplierForest_node_148348 else g32p_supplierForest_node_148381)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_148431 else g32p_supplierForest_node_148476) else (if i.val < 211 then g32p_supplierForest_node_148478 else g32p_supplierForest_node_148542)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_148543 else g32p_supplierForest_node_148550) else (if i.val < 215 then g32p_supplierForest_node_148611 else g32p_supplierForest_node_148646))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_148664 else g32p_supplierForest_node_148765) else (if i.val < 219 then g32p_supplierForest_node_148792 else g32p_supplierForest_node_148805)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_148889 else g32p_supplierForest_node_148942) else (if i.val < 223 then g32p_supplierForest_node_149011 else g32p_supplierForest_node_149024))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_149072 else g32p_supplierForest_node_149099) else (if i.val < 227 then g32p_supplierForest_node_149112 else g32p_supplierForest_node_149119)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_149121 else g32p_supplierForest_node_149124) else (if i.val < 231 then g32p_supplierForest_node_149128 else g32p_supplierForest_node_149187))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_149190 else g32p_supplierForest_node_149199) else (if i.val < 235 then g32p_supplierForest_node_149233 else g32p_supplierForest_node_149236)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_149239 else g32p_supplierForest_node_149267) else (if i.val < 239 then g32p_supplierForest_node_149269 else g32p_supplierForest_node_149341)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_149343 else g32p_supplierForest_node_149354) else (if i.val < 243 then g32p_supplierForest_node_149428 else g32p_supplierForest_node_149455)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_149459 else g32p_supplierForest_node_149529) else (if i.val < 247 then g32p_supplierForest_node_149535 else g32p_supplierForest_node_149557))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_149566 else g32p_supplierForest_node_149579) else (if i.val < 251 then g32p_supplierForest_node_149582 else g32p_supplierForest_node_149588)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_149598 else g32p_supplierForest_node_149639) else (if i.val < 255 then g32p_supplierForest_node_149640 else g32p_supplierForest_node_149717))))))))

def g32p_supplierForest_classes_130 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 42) else (if i.val < 3 then 38 else 38)) else (if i.val < 6 then (if i.val < 5 then 21 else 42) else (if i.val < 7 then 21 else 72))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 73 else 21) else (if i.val < 11 then 94 else 73)) else (if i.val < 14 then (if i.val < 13 then 38 else 38) else (if i.val < 15 then 70 else 73)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 73 else 38) else (if i.val < 19 then 38 else 72)) else (if i.val < 22 then (if i.val < 21 then 42 else 94) else (if i.val < 23 then 43 else 38))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 38 else 74) else (if i.val < 27 then 73 else 21)) else (if i.val < 30 then (if i.val < 29 then 73 else 73) else (if i.val < 31 then 73 else 38))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 73 else 74) else (if i.val < 35 then 73 else 73)) else (if i.val < 38 then (if i.val < 37 then 21 else 38) else (if i.val < 39 then 21 else 71))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 71 else 38) else (if i.val < 43 then 73 else 73)) else (if i.val < 46 then (if i.val < 45 then 72 else 21) else (if i.val < 47 then 43 else 42)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 73 else 38) else (if i.val < 51 then 38 else 21)) else (if i.val < 54 then (if i.val < 53 then 42 else 74) else (if i.val < 55 then 71 else 20))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 77 else 72) else (if i.val < 59 then 71 else 38)) else (if i.val < 62 then (if i.val < 61 then 21 else 75) else (if i.val < 63 then 71 else 73)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 43 else 72) else (if i.val < 67 then 42 else 22)) else (if i.val < 70 then (if i.val < 69 then 73 else 42) else (if i.val < 71 then 41 else 73))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 42 else 71) else (if i.val < 75 then 70 else 38)) else (if i.val < 78 then (if i.val < 77 then 38 else 21) else (if i.val < 79 then 21 else 73)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 71) else (if i.val < 83 then 43 else 71)) else (if i.val < 86 then (if i.val < 85 then 71 else 71) else (if i.val < 87 then 21 else 21))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 77 else 71) else (if i.val < 91 then 74 else 71)) else (if i.val < 94 then (if i.val < 93 then 71 else 38) else (if i.val < 95 then 73 else 38))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 73 else 73) else (if i.val < 99 then 94 else 73)) else (if i.val < 102 then (if i.val < 101 then 72 else 42) else (if i.val < 103 then 47 else 86))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 86 else 46) else (if i.val < 107 then 86 else 54)) else (if i.val < 110 then (if i.val < 109 then 46 else 53) else (if i.val < 111 then 26 else 46)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 49 else 46) else (if i.val < 115 then 53 else 47)) else (if i.val < 118 then (if i.val < 117 then 26 else 49) else (if i.val < 119 then 86 else 46))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 46 else 47) else (if i.val < 123 then 9 else 49)) else (if i.val < 126 then (if i.val < 125 then 49 else 53) else (if i.val < 127 then 45 else 46))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 47 else 47) else (if i.val < 131 then 46 else 47)) else (if i.val < 134 then (if i.val < 133 then 25 else 46) else (if i.val < 135 then 47 else 49))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 80 else 86) else (if i.val < 139 then 47 else 46)) else (if i.val < 142 then (if i.val < 141 then 46 else 49) else (if i.val < 143 then 26 else 46)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 82 else 55) else (if i.val < 147 then 47 else 49)) else (if i.val < 150 then (if i.val < 149 then 45 else 49) else (if i.val < 151 then 47 else 86))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 46 else 55) else (if i.val < 155 then 25 else 49)) else (if i.val < 158 then (if i.val < 157 then 49 else 49) else (if i.val < 159 then 86 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 53 else 49) else (if i.val < 163 then 25 else 86)) else (if i.val < 166 then (if i.val < 165 then 26 else 25) else (if i.val < 167 then 83 else 26))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 46 else 53) else (if i.val < 171 then 86 else 26)) else (if i.val < 174 then (if i.val < 173 then 47 else 46) else (if i.val < 175 then 55 else 83)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 46 else 84) else (if i.val < 179 then 46 else 25)) else (if i.val < 182 then (if i.val < 181 then 55 else 84) else (if i.val < 183 then 46 else 55))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 86) else (if i.val < 187 then 53 else 48)) else (if i.val < 190 then (if i.val < 189 then 50 else 53) else (if i.val < 191 then 49 else 49)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 46 else 47) else (if i.val < 195 then 25 else 26)) else (if i.val < 198 then (if i.val < 197 then 49 else 47) else (if i.val < 199 then 46 else 49))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 26 else 54) else (if i.val < 203 then 86 else 47)) else (if i.val < 206 then (if i.val < 205 then 49 else 49) else (if i.val < 207 then 86 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 49 else 54) else (if i.val < 211 then 49 else 86)) else (if i.val < 214 then (if i.val < 213 then 55 else 46) else (if i.val < 215 then 47 else 86))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 49 else 49) else (if i.val < 219 then 25 else 46)) else (if i.val < 222 then (if i.val < 221 then 49 else 80) else (if i.val < 223 then 55 else 55))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 49 else 50) else (if i.val < 227 then 54 else 53)) else (if i.val < 230 then (if i.val < 229 then 80 else 26) else (if i.val < 231 then 50 else 9))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 26 else 86) else (if i.val < 235 then 49 else 47)) else (if i.val < 238 then (if i.val < 237 then 46 else 86) else (if i.val < 239 then 47 else 83)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 25 else 46) else (if i.val < 243 then 49 else 50)) else (if i.val < 246 then (if i.val < 245 then 54 else 49) else (if i.val < 247 then 46 else 25))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 55 else 49) else (if i.val < 251 then 46 else 86)) else (if i.val < 254 then (if i.val < 253 then 54 else 86) else (if i.val < 255 then 86 else 54))))))))

theorem g32p_supplierForest_actual_130 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_130 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_130 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_141576
  · exact g32p_supplierForest_actual_141598
  · exact g32p_supplierForest_actual_141666
  · exact g32p_supplierForest_actual_141710
  · exact g32p_supplierForest_actual_141741
  · exact g32p_supplierForest_actual_141747
  · exact g32p_supplierForest_actual_141862
  · exact g32p_supplierForest_actual_141869
  · exact g32p_supplierForest_actual_141936
  · exact g32p_supplierForest_actual_141943
  · exact g32p_supplierForest_actual_141963
  · exact g32p_supplierForest_actual_141970
  · exact g32p_supplierForest_actual_141975
  · exact g32p_supplierForest_actual_142000
  · exact g32p_supplierForest_actual_142005
  · exact g32p_supplierForest_actual_142020
  · exact g32p_supplierForest_actual_142021
  · exact g32p_supplierForest_actual_142041
  · exact g32p_supplierForest_actual_142057
  · exact g32p_supplierForest_actual_142093
  · exact g32p_supplierForest_actual_142165
  · exact g32p_supplierForest_actual_142224
  · exact g32p_supplierForest_actual_142246
  · exact g32p_supplierForest_actual_142288
  · exact g32p_supplierForest_actual_142370
  · exact g32p_supplierForest_actual_142384
  · exact g32p_supplierForest_actual_142410
  · exact g32p_supplierForest_actual_142431
  · exact g32p_supplierForest_actual_142454
  · exact g32p_supplierForest_actual_142455
  · exact g32p_supplierForest_actual_142479
  · exact g32p_supplierForest_actual_142491
  · exact g32p_supplierForest_actual_142511
  · exact g32p_supplierForest_actual_142539
  · exact g32p_supplierForest_actual_142558
  · exact g32p_supplierForest_actual_142582
  · exact g32p_supplierForest_actual_142607
  · exact g32p_supplierForest_actual_142611
  · exact g32p_supplierForest_actual_142622
  · exact g32p_supplierForest_actual_142659
  · exact g32p_supplierForest_actual_142660
  · exact g32p_supplierForest_actual_142668
  · exact g32p_supplierForest_actual_142736
  · exact g32p_supplierForest_actual_142744
  · exact g32p_supplierForest_actual_142748
  · exact g32p_supplierForest_actual_142761
  · exact g32p_supplierForest_actual_142780
  · exact g32p_supplierForest_actual_142796
  · exact g32p_supplierForest_actual_142806
  · exact g32p_supplierForest_actual_142810
  · exact g32p_supplierForest_actual_142816
  · exact g32p_supplierForest_actual_142827
  · exact g32p_supplierForest_actual_142925
  · exact g32p_supplierForest_actual_142927
  · exact g32p_supplierForest_actual_142971
  · exact g32p_supplierForest_actual_142984
  · exact g32p_supplierForest_actual_143070
  · exact g32p_supplierForest_actual_143094
  · exact g32p_supplierForest_actual_143162
  · exact g32p_supplierForest_actual_143182
  · exact g32p_supplierForest_actual_143193
  · exact g32p_supplierForest_actual_143206
  · exact g32p_supplierForest_actual_143211
  · exact g32p_supplierForest_actual_143263
  · exact g32p_supplierForest_actual_143317
  · exact g32p_supplierForest_actual_143349
  · exact g32p_supplierForest_actual_143409
  · exact g32p_supplierForest_actual_143438
  · exact g32p_supplierForest_actual_143456
  · exact g32p_supplierForest_actual_143457
  · exact g32p_supplierForest_actual_143462
  · exact g32p_supplierForest_actual_143473
  · exact g32p_supplierForest_actual_143509
  · exact g32p_supplierForest_actual_143542
  · exact g32p_supplierForest_actual_143561
  · exact g32p_supplierForest_actual_143606
  · exact g32p_supplierForest_actual_143631
  · exact g32p_supplierForest_actual_143683
  · exact g32p_supplierForest_actual_143700
  · exact g32p_supplierForest_actual_143737
  · exact g32p_supplierForest_actual_143817
  · exact g32p_supplierForest_actual_143828
  · exact g32p_supplierForest_actual_143838
  · exact g32p_supplierForest_actual_143907
  · exact g32p_supplierForest_actual_143921
  · exact g32p_supplierForest_actual_143940
  · exact g32p_supplierForest_actual_143982
  · exact g32p_supplierForest_actual_143990
  · exact g32p_supplierForest_actual_143995
  · exact g32p_supplierForest_actual_144004
  · exact g32p_supplierForest_actual_144012
  · exact g32p_supplierForest_actual_144056
  · exact g32p_supplierForest_actual_144075
  · exact g32p_supplierForest_actual_144092
  · exact g32p_supplierForest_actual_144093
  · exact g32p_supplierForest_actual_144104
  · exact g32p_supplierForest_actual_144129
  · exact g32p_supplierForest_actual_144226
  · exact g32p_supplierForest_actual_144246
  · exact g32p_supplierForest_actual_144386
  · exact g32p_supplierForest_actual_144406
  · exact g32p_supplierForest_actual_144464
  · exact g32p_supplierForest_actual_144643
  · exact g32p_supplierForest_actual_144710
  · exact g32p_supplierForest_actual_144728
  · exact g32p_supplierForest_actual_144748
  · exact g32p_supplierForest_actual_144759
  · exact g32p_supplierForest_actual_144786
  · exact g32p_supplierForest_actual_144794
  · exact g32p_supplierForest_actual_144834
  · exact g32p_supplierForest_actual_144877
  · exact g32p_supplierForest_actual_144894
  · exact g32p_supplierForest_actual_145059
  · exact g32p_supplierForest_actual_145071
  · exact g32p_supplierForest_actual_145094
  · exact g32p_supplierForest_actual_145118
  · exact g32p_supplierForest_actual_145140
  · exact g32p_supplierForest_actual_145141
  · exact g32p_supplierForest_actual_145188
  · exact g32p_supplierForest_actual_145190
  · exact g32p_supplierForest_actual_145233
  · exact g32p_supplierForest_actual_145236
  · exact g32p_supplierForest_actual_145252
  · exact g32p_supplierForest_actual_145286
  · exact g32p_supplierForest_actual_145314
  · exact g32p_supplierForest_actual_145335
  · exact g32p_supplierForest_actual_145393
  · exact g32p_supplierForest_actual_145454
  · exact g32p_supplierForest_actual_145507
  · exact g32p_supplierForest_actual_145559
  · exact g32p_supplierForest_actual_145569
  · exact g32p_supplierForest_actual_145597
  · exact g32p_supplierForest_actual_145624
  · exact g32p_supplierForest_actual_145637
  · exact g32p_supplierForest_actual_145707
  · exact g32p_supplierForest_actual_145745
  · exact g32p_supplierForest_actual_145828
  · exact g32p_supplierForest_actual_145868
  · exact g32p_supplierForest_actual_145900
  · exact g32p_supplierForest_actual_145919
  · exact g32p_supplierForest_actual_145929
  · exact g32p_supplierForest_actual_145940
  · exact g32p_supplierForest_actual_145965
  · exact g32p_supplierForest_actual_145984
  · exact g32p_supplierForest_actual_146010
  · exact g32p_supplierForest_actual_146025
  · exact g32p_supplierForest_actual_146082
  · exact g32p_supplierForest_actual_146164
  · exact g32p_supplierForest_actual_146184
  · exact g32p_supplierForest_actual_146194
  · exact g32p_supplierForest_actual_146288
  · exact g32p_supplierForest_actual_146317
  · exact g32p_supplierForest_actual_146348
  · exact g32p_supplierForest_actual_146382
  · exact g32p_supplierForest_actual_146562
  · exact g32p_supplierForest_actual_146728
  · exact g32p_supplierForest_actual_146768
  · exact g32p_supplierForest_actual_146770
  · exact g32p_supplierForest_actual_146777
  · exact g32p_supplierForest_actual_146786
  · exact g32p_supplierForest_actual_146790
  · exact g32p_supplierForest_actual_146797
  · exact g32p_supplierForest_actual_146897
  · exact g32p_supplierForest_actual_146955
  · exact g32p_supplierForest_actual_146983
  · exact g32p_supplierForest_actual_147002
  · exact g32p_supplierForest_actual_147107
  · exact g32p_supplierForest_actual_147147
  · exact g32p_supplierForest_actual_147152
  · exact g32p_supplierForest_actual_147169
  · exact g32p_supplierForest_actual_147196
  · exact g32p_supplierForest_actual_147211
  · exact g32p_supplierForest_actual_147235
  · exact g32p_supplierForest_actual_147239
  · exact g32p_supplierForest_actual_147282
  · exact g32p_supplierForest_actual_147324
  · exact g32p_supplierForest_actual_147403
  · exact g32p_supplierForest_actual_147409
  · exact g32p_supplierForest_actual_147451
  · exact g32p_supplierForest_actual_147471
  · exact g32p_supplierForest_actual_147577
  · exact g32p_supplierForest_actual_147602
  · exact g32p_supplierForest_actual_147611
  · exact g32p_supplierForest_actual_147619
  · exact g32p_supplierForest_actual_147621
  · exact g32p_supplierForest_actual_147629
  · exact g32p_supplierForest_actual_147667
  · exact g32p_supplierForest_actual_147680
  · exact g32p_supplierForest_actual_147794
  · exact g32p_supplierForest_actual_147796
  · exact g32p_supplierForest_actual_147800
  · exact g32p_supplierForest_actual_147810
  · exact g32p_supplierForest_actual_147871
  · exact g32p_supplierForest_actual_147930
  · exact g32p_supplierForest_actual_147956
  · exact g32p_supplierForest_actual_147990
  · exact g32p_supplierForest_actual_147998
  · exact g32p_supplierForest_actual_148035
  · exact g32p_supplierForest_actual_148075
  · exact g32p_supplierForest_actual_148079
  · exact g32p_supplierForest_actual_148132
  · exact g32p_supplierForest_actual_148233
  · exact g32p_supplierForest_actual_148272
  · exact g32p_supplierForest_actual_148312
  · exact g32p_supplierForest_actual_148325
  · exact g32p_supplierForest_actual_148346
  · exact g32p_supplierForest_actual_148348
  · exact g32p_supplierForest_actual_148381
  · exact g32p_supplierForest_actual_148431
  · exact g32p_supplierForest_actual_148476
  · exact g32p_supplierForest_actual_148478
  · exact g32p_supplierForest_actual_148542
  · exact g32p_supplierForest_actual_148543
  · exact g32p_supplierForest_actual_148550
  · exact g32p_supplierForest_actual_148611
  · exact g32p_supplierForest_actual_148646
  · exact g32p_supplierForest_actual_148664
  · exact g32p_supplierForest_actual_148765
  · exact g32p_supplierForest_actual_148792
  · exact g32p_supplierForest_actual_148805
  · exact g32p_supplierForest_actual_148889
  · exact g32p_supplierForest_actual_148942
  · exact g32p_supplierForest_actual_149011
  · exact g32p_supplierForest_actual_149024
  · exact g32p_supplierForest_actual_149072
  · exact g32p_supplierForest_actual_149099
  · exact g32p_supplierForest_actual_149112
  · exact g32p_supplierForest_actual_149119
  · exact g32p_supplierForest_actual_149121
  · exact g32p_supplierForest_actual_149124
  · exact g32p_supplierForest_actual_149128
  · exact g32p_supplierForest_actual_149187
  · exact g32p_supplierForest_actual_149190
  · exact g32p_supplierForest_actual_149199
  · exact g32p_supplierForest_actual_149233
  · exact g32p_supplierForest_actual_149236
  · exact g32p_supplierForest_actual_149239
  · exact g32p_supplierForest_actual_149267
  · exact g32p_supplierForest_actual_149269
  · exact g32p_supplierForest_actual_149341
  · exact g32p_supplierForest_actual_149343
  · exact g32p_supplierForest_actual_149354
  · exact g32p_supplierForest_actual_149428
  · exact g32p_supplierForest_actual_149455
  · exact g32p_supplierForest_actual_149459
  · exact g32p_supplierForest_actual_149529
  · exact g32p_supplierForest_actual_149535
  · exact g32p_supplierForest_actual_149557
  · exact g32p_supplierForest_actual_149566
  · exact g32p_supplierForest_actual_149579
  · exact g32p_supplierForest_actual_149582
  · exact g32p_supplierForest_actual_149588
  · exact g32p_supplierForest_actual_149598
  · exact g32p_supplierForest_actual_149639
  · exact g32p_supplierForest_actual_149640
  · exact g32p_supplierForest_actual_149717

def g32p_supplierForest_nodes_131 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_149831 else g32p_supplierForest_node_149869) else (if i.val < 3 then g32p_supplierForest_node_149889 else g32p_supplierForest_node_149922)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_149934 else g32p_supplierForest_node_149942) else (if i.val < 7 then g32p_supplierForest_node_149946 else g32p_supplierForest_node_149990))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_150009 else g32p_supplierForest_node_150042) else (if i.val < 11 then g32p_supplierForest_node_150065 else g32p_supplierForest_node_150078)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_150080 else g32p_supplierForest_node_150099) else (if i.val < 15 then g32p_supplierForest_node_150116 else g32p_supplierForest_node_150189)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_150261 else g32p_supplierForest_node_150267) else (if i.val < 19 then g32p_supplierForest_node_150273 else g32p_supplierForest_node_150287)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_150292 else g32p_supplierForest_node_150302) else (if i.val < 23 then g32p_supplierForest_node_150380 else g32p_supplierForest_node_150453))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_150600 else g32p_supplierForest_node_150613) else (if i.val < 27 then g32p_supplierForest_node_150662 else g32p_supplierForest_node_150665)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_150696 else g32p_supplierForest_node_150697) else (if i.val < 31 then g32p_supplierForest_node_150719 else g32p_supplierForest_node_150727))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_150775 else g32p_supplierForest_node_150778) else (if i.val < 35 then g32p_supplierForest_node_150812 else g32p_supplierForest_node_150865)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_150908 else g32p_supplierForest_node_150916) else (if i.val < 39 then g32p_supplierForest_node_150953 else g32p_supplierForest_node_151017))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_151026 else g32p_supplierForest_node_151039) else (if i.val < 43 then g32p_supplierForest_node_151061 else g32p_supplierForest_node_151066)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_151078 else g32p_supplierForest_node_151112) else (if i.val < 47 then g32p_supplierForest_node_151142 else g32p_supplierForest_node_151148)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_151156 else g32p_supplierForest_node_151161) else (if i.val < 51 then g32p_supplierForest_node_151168 else g32p_supplierForest_node_151176)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_151208 else g32p_supplierForest_node_151257) else (if i.val < 55 then g32p_supplierForest_node_151265 else g32p_supplierForest_node_151281))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_151305 else g32p_supplierForest_node_151334) else (if i.val < 59 then g32p_supplierForest_node_151348 else g32p_supplierForest_node_151389)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_151412 else g32p_supplierForest_node_151442) else (if i.val < 63 then g32p_supplierForest_node_151447 else g32p_supplierForest_node_151478)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_151483 else g32p_supplierForest_node_151501) else (if i.val < 67 then g32p_supplierForest_node_151509 else g32p_supplierForest_node_151543)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_151546 else g32p_supplierForest_node_151598) else (if i.val < 71 then g32p_supplierForest_node_151638 else g32p_supplierForest_node_151661))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_151704 else g32p_supplierForest_node_151726) else (if i.val < 75 then g32p_supplierForest_node_151759 else g32p_supplierForest_node_151775)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_151921 else g32p_supplierForest_node_151926) else (if i.val < 79 then g32p_supplierForest_node_151932 else g32p_supplierForest_node_151958)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_152008 else g32p_supplierForest_node_152014) else (if i.val < 83 then g32p_supplierForest_node_152062 else g32p_supplierForest_node_152076)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_152111 else g32p_supplierForest_node_152214) else (if i.val < 87 then g32p_supplierForest_node_152232 else g32p_supplierForest_node_152237))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_152244 else g32p_supplierForest_node_152347) else (if i.val < 91 then g32p_supplierForest_node_152363 else g32p_supplierForest_node_152385)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_152430 else g32p_supplierForest_node_152434) else (if i.val < 95 then g32p_supplierForest_node_152535 else g32p_supplierForest_node_152565))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_152603 else g32p_supplierForest_node_152647) else (if i.val < 99 then g32p_supplierForest_node_152664 else g32p_supplierForest_node_152869)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_152871 else g32p_supplierForest_node_152889) else (if i.val < 103 then g32p_supplierForest_node_152926 else g32p_supplierForest_node_152973))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_152990 else g32p_supplierForest_node_153005) else (if i.val < 107 then g32p_supplierForest_node_153060 else g32p_supplierForest_node_153087)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_153104 else g32p_supplierForest_node_153217) else (if i.val < 111 then g32p_supplierForest_node_153265 else g32p_supplierForest_node_153277)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_153303 else g32p_supplierForest_node_153341) else (if i.val < 115 then g32p_supplierForest_node_153359 else g32p_supplierForest_node_153429)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_153432 else g32p_supplierForest_node_153433) else (if i.val < 119 then g32p_supplierForest_node_153472 else g32p_supplierForest_node_153582))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_153616 else g32p_supplierForest_node_153664) else (if i.val < 123 then g32p_supplierForest_node_153743 else g32p_supplierForest_node_153753)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_153762 else g32p_supplierForest_node_153776) else (if i.val < 127 then g32p_supplierForest_node_153818 else g32p_supplierForest_node_153820))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_153844 else g32p_supplierForest_node_153884) else (if i.val < 131 then g32p_supplierForest_node_153978 else g32p_supplierForest_node_154071)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_154151 else g32p_supplierForest_node_154223) else (if i.val < 135 then g32p_supplierForest_node_154225 else g32p_supplierForest_node_154238))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_154361 else g32p_supplierForest_node_154382) else (if i.val < 139 then g32p_supplierForest_node_154415 else g32p_supplierForest_node_154459)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_154476 else g32p_supplierForest_node_154486) else (if i.val < 143 then g32p_supplierForest_node_154492 else g32p_supplierForest_node_154500)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_154655 else g32p_supplierForest_node_154673) else (if i.val < 147 then g32p_supplierForest_node_154748 else g32p_supplierForest_node_154754)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_154776 else g32p_supplierForest_node_154787) else (if i.val < 151 then g32p_supplierForest_node_154794 else g32p_supplierForest_node_154839))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_154877 else g32p_supplierForest_node_154975) else (if i.val < 155 then g32p_supplierForest_node_154978 else g32p_supplierForest_node_155007)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_155155 else g32p_supplierForest_node_155372) else (if i.val < 159 then g32p_supplierForest_node_155403 else g32p_supplierForest_node_000494))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_000571 else g32p_supplierForest_node_000660) else (if i.val < 163 then g32p_supplierForest_node_001015 else g32p_supplierForest_node_001020)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_001043 else g32p_supplierForest_node_001049) else (if i.val < 167 then g32p_supplierForest_node_001071 else g32p_supplierForest_node_001094))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_001143 else g32p_supplierForest_node_001353) else (if i.val < 171 then g32p_supplierForest_node_001407 else g32p_supplierForest_node_001448)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_001531 else g32p_supplierForest_node_001556) else (if i.val < 175 then g32p_supplierForest_node_001641 else g32p_supplierForest_node_001765)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_001861 else g32p_supplierForest_node_002028) else (if i.val < 179 then g32p_supplierForest_node_002385 else g32p_supplierForest_node_002400)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_002486 else g32p_supplierForest_node_002596) else (if i.val < 183 then g32p_supplierForest_node_002883 else g32p_supplierForest_node_002963))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_003081 else g32p_supplierForest_node_003142) else (if i.val < 187 then g32p_supplierForest_node_003212 else g32p_supplierForest_node_003252)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_003366 else g32p_supplierForest_node_003531) else (if i.val < 191 then g32p_supplierForest_node_003571 else g32p_supplierForest_node_003572)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_003603 else g32p_supplierForest_node_003616) else (if i.val < 195 then g32p_supplierForest_node_003651 else g32p_supplierForest_node_003680)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_003709 else g32p_supplierForest_node_003770) else (if i.val < 199 then g32p_supplierForest_node_003777 else g32p_supplierForest_node_003833))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_003918 else g32p_supplierForest_node_003930) else (if i.val < 203 then g32p_supplierForest_node_003977 else g32p_supplierForest_node_003990)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_004075 else g32p_supplierForest_node_004079) else (if i.val < 207 then g32p_supplierForest_node_004097 else g32p_supplierForest_node_004123)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_004131 else g32p_supplierForest_node_004253) else (if i.val < 211 then g32p_supplierForest_node_004261 else g32p_supplierForest_node_004433)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_004487 else g32p_supplierForest_node_004590) else (if i.val < 215 then g32p_supplierForest_node_004662 else g32p_supplierForest_node_004725))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_004761 else g32p_supplierForest_node_004788) else (if i.val < 219 then g32p_supplierForest_node_004877 else g32p_supplierForest_node_004895)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_004947 else g32p_supplierForest_node_004949) else (if i.val < 223 then g32p_supplierForest_node_005055 else g32p_supplierForest_node_005151))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_005190 else g32p_supplierForest_node_005220) else (if i.val < 227 then g32p_supplierForest_node_005317 else g32p_supplierForest_node_005336)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_005462 else g32p_supplierForest_node_005590) else (if i.val < 231 then g32p_supplierForest_node_005653 else g32p_supplierForest_node_005709))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_005732 else g32p_supplierForest_node_005745) else (if i.val < 235 then g32p_supplierForest_node_005751 else g32p_supplierForest_node_005885)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_005922 else g32p_supplierForest_node_005977) else (if i.val < 239 then g32p_supplierForest_node_006010 else g32p_supplierForest_node_006119)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_006225 else g32p_supplierForest_node_006306) else (if i.val < 243 then g32p_supplierForest_node_006334 else g32p_supplierForest_node_006355)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_006436 else g32p_supplierForest_node_006580) else (if i.val < 247 then g32p_supplierForest_node_006585 else g32p_supplierForest_node_006612))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_006630 else g32p_supplierForest_node_006649) else (if i.val < 251 then g32p_supplierForest_node_006688 else g32p_supplierForest_node_006726)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_006745 else g32p_supplierForest_node_006932) else (if i.val < 255 then g32p_supplierForest_node_006950 else g32p_supplierForest_node_007099))))))))

def g32p_supplierForest_classes_131 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 54 else 86) else (if i.val < 3 then 49 else 25)) else (if i.val < 6 then (if i.val < 5 then 54 else 53) else (if i.val < 7 then 86 else 26))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 54 else 86) else (if i.val < 11 then 86 else 49)) else (if i.val < 14 then (if i.val < 13 then 47 else 49) else (if i.val < 15 then 53 else 54)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 86 else 86) else (if i.val < 19 then 86 else 47)) else (if i.val < 22 then (if i.val < 21 then 45 else 86) else (if i.val < 23 then 54 else 55))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 86) else (if i.val < 27 then 46 else 49)) else (if i.val < 30 then (if i.val < 29 then 52 else 25) else (if i.val < 31 then 47 else 49))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 86 else 55) else (if i.val < 35 then 46 else 54)) else (if i.val < 38 then (if i.val < 37 then 86 else 46) else (if i.val < 39 then 49 else 46))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 47 else 46) else (if i.val < 43 then 49 else 55)) else (if i.val < 46 then (if i.val < 45 then 86 else 49) else (if i.val < 47 then 86 else 54)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 55 else 49) else (if i.val < 51 then 86 else 54)) else (if i.val < 54 then (if i.val < 53 then 47 else 9) else (if i.val < 55 then 49 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 49) else (if i.val < 59 then 86 else 49)) else (if i.val < 62 then (if i.val < 61 then 86 else 49) else (if i.val < 63 then 47 else 46)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 84 else 46) else (if i.val < 67 then 47 else 49)) else (if i.val < 70 then (if i.val < 69 then 56 else 86) else (if i.val < 71 then 47 else 53))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 46 else 26) else (if i.val < 75 then 86 else 49)) else (if i.val < 78 then (if i.val < 77 then 86 else 49) else (if i.val < 79 then 86 else 49)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 86 else 49) else (if i.val < 83 then 49 else 26)) else (if i.val < 86 then (if i.val < 85 then 86 else 54) else (if i.val < 87 then 49 else 25))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 26 else 80) else (if i.val < 91 then 86 else 11)) else (if i.val < 94 then (if i.val < 93 then 26 else 25) else (if i.val < 95 then 15 else 61))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 30 else 30) else (if i.val < 99 then 61 else 89)) else (if i.val < 102 then (if i.val < 101 then 29 else 60) else (if i.val < 103 then 30 else 62))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 59 else 60) else (if i.val < 107 then 60 else 30)) else (if i.val < 110 then (if i.val < 109 then 66 else 90) else (if i.val < 111 then 61 else 57)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 57 else 62) else (if i.val < 115 then 30 else 57)) else (if i.val < 118 then (if i.val < 117 then 57 else 30) else (if i.val < 119 then 36 else 66))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 62 else 57) else (if i.val < 123 then 90 else 30)) else (if i.val < 126 then (if i.val < 125 then 15 else 60) else (if i.val < 127 then 30 else 61))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 60 else 89) else (if i.val < 131 then 60 else 30)) else (if i.val < 134 then (if i.val < 133 then 60 else 62) else (if i.val < 135 then 57 else 66))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 59 else 66) else (if i.val < 139 then 17 else 30)) else (if i.val < 142 then (if i.val < 141 then 62 else 63) else (if i.val < 143 then 60 else 30)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 57 else 60) else (if i.val < 147 then 30 else 57)) else (if i.val < 150 then (if i.val < 149 then 60 else 57) else (if i.val < 151 then 57 else 57))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 35) else (if i.val < 155 then 35 else 21)) else (if i.val < 158 then (if i.val < 157 then 71 else 71) else (if i.val < 159 then 71 else 7))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 21 else 21) else (if i.val < 163 then 21 else 22)) else (if i.val < 166 then (if i.val < 165 then 21 else 21) else (if i.val < 167 then 21 else 25))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 26 else 12) else (if i.val < 171 then 10 else 26)) else (if i.val < 174 then (if i.val < 173 then 9 else 10) else (if i.val < 175 then 25 else 12)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 10 else 26) else (if i.val < 179 then 27 else 10)) else (if i.val < 182 then (if i.val < 181 then 26 else 30) else (if i.val < 183 then 30 else 29))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 14 else 16) else (if i.val < 187 then 16 else 14)) else (if i.val < 190 then (if i.val < 189 then 30 else 17) else (if i.val < 191 then 17 else 17)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 30 else 17) else (if i.val < 195 then 15 else 15)) else (if i.val < 198 then (if i.val < 197 then 15 else 30) else (if i.val < 199 then 16 else 30))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 17 else 15) else (if i.val < 203 then 30 else 16)) else (if i.val < 206 then (if i.val < 205 then 16 else 14) else (if i.val < 207 then 30 else 15)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 14 else 16) else (if i.val < 211 then 14 else 15)) else (if i.val < 214 then (if i.val < 213 then 30 else 17) else (if i.val < 215 then 30 else 16))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 30 else 16) else (if i.val < 219 then 30 else 16)) else (if i.val < 222 then (if i.val < 221 then 14 else 16) else (if i.val < 223 then 16 else 30))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 17 else 30) else (if i.val < 227 then 16 else 16)) else (if i.val < 230 then (if i.val < 229 then 30 else 16) else (if i.val < 231 then 17 else 14))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 16 else 29) else (if i.val < 235 then 16 else 38)) else (if i.val < 238 then (if i.val < 237 then 40 else 22) else (if i.val < 239 then 22 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 21 else 21) else (if i.val < 243 then 21 else 21)) else (if i.val < 246 then (if i.val < 245 then 7 else 38) else (if i.val < 247 then 21 else 21))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 21 else 20) else (if i.val < 251 then 22 else 38)) else (if i.val < 254 then (if i.val < 253 then 40 else 21) else (if i.val < 255 then 21 else 21))))))))

theorem g32p_supplierForest_actual_131 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_131 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_131 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_149831
  · exact g32p_supplierForest_actual_149869
  · exact g32p_supplierForest_actual_149889
  · exact g32p_supplierForest_actual_149922
  · exact g32p_supplierForest_actual_149934
  · exact g32p_supplierForest_actual_149942
  · exact g32p_supplierForest_actual_149946
  · exact g32p_supplierForest_actual_149990
  · exact g32p_supplierForest_actual_150009
  · exact g32p_supplierForest_actual_150042
  · exact g32p_supplierForest_actual_150065
  · exact g32p_supplierForest_actual_150078
  · exact g32p_supplierForest_actual_150080
  · exact g32p_supplierForest_actual_150099
  · exact g32p_supplierForest_actual_150116
  · exact g32p_supplierForest_actual_150189
  · exact g32p_supplierForest_actual_150261
  · exact g32p_supplierForest_actual_150267
  · exact g32p_supplierForest_actual_150273
  · exact g32p_supplierForest_actual_150287
  · exact g32p_supplierForest_actual_150292
  · exact g32p_supplierForest_actual_150302
  · exact g32p_supplierForest_actual_150380
  · exact g32p_supplierForest_actual_150453
  · exact g32p_supplierForest_actual_150600
  · exact g32p_supplierForest_actual_150613
  · exact g32p_supplierForest_actual_150662
  · exact g32p_supplierForest_actual_150665
  · exact g32p_supplierForest_actual_150696
  · exact g32p_supplierForest_actual_150697
  · exact g32p_supplierForest_actual_150719
  · exact g32p_supplierForest_actual_150727
  · exact g32p_supplierForest_actual_150775
  · exact g32p_supplierForest_actual_150778
  · exact g32p_supplierForest_actual_150812
  · exact g32p_supplierForest_actual_150865
  · exact g32p_supplierForest_actual_150908
  · exact g32p_supplierForest_actual_150916
  · exact g32p_supplierForest_actual_150953
  · exact g32p_supplierForest_actual_151017
  · exact g32p_supplierForest_actual_151026
  · exact g32p_supplierForest_actual_151039
  · exact g32p_supplierForest_actual_151061
  · exact g32p_supplierForest_actual_151066
  · exact g32p_supplierForest_actual_151078
  · exact g32p_supplierForest_actual_151112
  · exact g32p_supplierForest_actual_151142
  · exact g32p_supplierForest_actual_151148
  · exact g32p_supplierForest_actual_151156
  · exact g32p_supplierForest_actual_151161
  · exact g32p_supplierForest_actual_151168
  · exact g32p_supplierForest_actual_151176
  · exact g32p_supplierForest_actual_151208
  · exact g32p_supplierForest_actual_151257
  · exact g32p_supplierForest_actual_151265
  · exact g32p_supplierForest_actual_151281
  · exact g32p_supplierForest_actual_151305
  · exact g32p_supplierForest_actual_151334
  · exact g32p_supplierForest_actual_151348
  · exact g32p_supplierForest_actual_151389
  · exact g32p_supplierForest_actual_151412
  · exact g32p_supplierForest_actual_151442
  · exact g32p_supplierForest_actual_151447
  · exact g32p_supplierForest_actual_151478
  · exact g32p_supplierForest_actual_151483
  · exact g32p_supplierForest_actual_151501
  · exact g32p_supplierForest_actual_151509
  · exact g32p_supplierForest_actual_151543
  · exact g32p_supplierForest_actual_151546
  · exact g32p_supplierForest_actual_151598
  · exact g32p_supplierForest_actual_151638
  · exact g32p_supplierForest_actual_151661
  · exact g32p_supplierForest_actual_151704
  · exact g32p_supplierForest_actual_151726
  · exact g32p_supplierForest_actual_151759
  · exact g32p_supplierForest_actual_151775
  · exact g32p_supplierForest_actual_151921
  · exact g32p_supplierForest_actual_151926
  · exact g32p_supplierForest_actual_151932
  · exact g32p_supplierForest_actual_151958
  · exact g32p_supplierForest_actual_152008
  · exact g32p_supplierForest_actual_152014
  · exact g32p_supplierForest_actual_152062
  · exact g32p_supplierForest_actual_152076
  · exact g32p_supplierForest_actual_152111
  · exact g32p_supplierForest_actual_152214
  · exact g32p_supplierForest_actual_152232
  · exact g32p_supplierForest_actual_152237
  · exact g32p_supplierForest_actual_152244
  · exact g32p_supplierForest_actual_152347
  · exact g32p_supplierForest_actual_152363
  · exact g32p_supplierForest_actual_152385
  · exact g32p_supplierForest_actual_152430
  · exact g32p_supplierForest_actual_152434
  · exact g32p_supplierForest_actual_152535
  · exact g32p_supplierForest_actual_152565
  · exact g32p_supplierForest_actual_152603
  · exact g32p_supplierForest_actual_152647
  · exact g32p_supplierForest_actual_152664
  · exact g32p_supplierForest_actual_152869
  · exact g32p_supplierForest_actual_152871
  · exact g32p_supplierForest_actual_152889
  · exact g32p_supplierForest_actual_152926
  · exact g32p_supplierForest_actual_152973
  · exact g32p_supplierForest_actual_152990
  · exact g32p_supplierForest_actual_153005
  · exact g32p_supplierForest_actual_153060
  · exact g32p_supplierForest_actual_153087
  · exact g32p_supplierForest_actual_153104
  · exact g32p_supplierForest_actual_153217
  · exact g32p_supplierForest_actual_153265
  · exact g32p_supplierForest_actual_153277
  · exact g32p_supplierForest_actual_153303
  · exact g32p_supplierForest_actual_153341
  · exact g32p_supplierForest_actual_153359
  · exact g32p_supplierForest_actual_153429
  · exact g32p_supplierForest_actual_153432
  · exact g32p_supplierForest_actual_153433
  · exact g32p_supplierForest_actual_153472
  · exact g32p_supplierForest_actual_153582
  · exact g32p_supplierForest_actual_153616
  · exact g32p_supplierForest_actual_153664
  · exact g32p_supplierForest_actual_153743
  · exact g32p_supplierForest_actual_153753
  · exact g32p_supplierForest_actual_153762
  · exact g32p_supplierForest_actual_153776
  · exact g32p_supplierForest_actual_153818
  · exact g32p_supplierForest_actual_153820
  · exact g32p_supplierForest_actual_153844
  · exact g32p_supplierForest_actual_153884
  · exact g32p_supplierForest_actual_153978
  · exact g32p_supplierForest_actual_154071
  · exact g32p_supplierForest_actual_154151
  · exact g32p_supplierForest_actual_154223
  · exact g32p_supplierForest_actual_154225
  · exact g32p_supplierForest_actual_154238
  · exact g32p_supplierForest_actual_154361
  · exact g32p_supplierForest_actual_154382
  · exact g32p_supplierForest_actual_154415
  · exact g32p_supplierForest_actual_154459
  · exact g32p_supplierForest_actual_154476
  · exact g32p_supplierForest_actual_154486
  · exact g32p_supplierForest_actual_154492
  · exact g32p_supplierForest_actual_154500
  · exact g32p_supplierForest_actual_154655
  · exact g32p_supplierForest_actual_154673
  · exact g32p_supplierForest_actual_154748
  · exact g32p_supplierForest_actual_154754
  · exact g32p_supplierForest_actual_154776
  · exact g32p_supplierForest_actual_154787
  · exact g32p_supplierForest_actual_154794
  · exact g32p_supplierForest_actual_154839
  · exact g32p_supplierForest_actual_154877
  · exact g32p_supplierForest_actual_154975
  · exact g32p_supplierForest_actual_154978
  · exact g32p_supplierForest_actual_155007
  · exact g32p_supplierForest_actual_155155
  · exact g32p_supplierForest_actual_155372
  · exact g32p_supplierForest_actual_155403
  · exact g32p_supplierForest_actual_000494
  · exact g32p_supplierForest_actual_000571
  · exact g32p_supplierForest_actual_000660
  · exact g32p_supplierForest_actual_001015
  · exact g32p_supplierForest_actual_001020
  · exact g32p_supplierForest_actual_001043
  · exact g32p_supplierForest_actual_001049
  · exact g32p_supplierForest_actual_001071
  · exact g32p_supplierForest_actual_001094
  · exact g32p_supplierForest_actual_001143
  · exact g32p_supplierForest_actual_001353
  · exact g32p_supplierForest_actual_001407
  · exact g32p_supplierForest_actual_001448
  · exact g32p_supplierForest_actual_001531
  · exact g32p_supplierForest_actual_001556
  · exact g32p_supplierForest_actual_001641
  · exact g32p_supplierForest_actual_001765
  · exact g32p_supplierForest_actual_001861
  · exact g32p_supplierForest_actual_002028
  · exact g32p_supplierForest_actual_002385
  · exact g32p_supplierForest_actual_002400
  · exact g32p_supplierForest_actual_002486
  · exact g32p_supplierForest_actual_002596
  · exact g32p_supplierForest_actual_002883
  · exact g32p_supplierForest_actual_002963
  · exact g32p_supplierForest_actual_003081
  · exact g32p_supplierForest_actual_003142
  · exact g32p_supplierForest_actual_003212
  · exact g32p_supplierForest_actual_003252
  · exact g32p_supplierForest_actual_003366
  · exact g32p_supplierForest_actual_003531
  · exact g32p_supplierForest_actual_003571
  · exact g32p_supplierForest_actual_003572
  · exact g32p_supplierForest_actual_003603
  · exact g32p_supplierForest_actual_003616
  · exact g32p_supplierForest_actual_003651
  · exact g32p_supplierForest_actual_003680
  · exact g32p_supplierForest_actual_003709
  · exact g32p_supplierForest_actual_003770
  · exact g32p_supplierForest_actual_003777
  · exact g32p_supplierForest_actual_003833
  · exact g32p_supplierForest_actual_003918
  · exact g32p_supplierForest_actual_003930
  · exact g32p_supplierForest_actual_003977
  · exact g32p_supplierForest_actual_003990
  · exact g32p_supplierForest_actual_004075
  · exact g32p_supplierForest_actual_004079
  · exact g32p_supplierForest_actual_004097
  · exact g32p_supplierForest_actual_004123
  · exact g32p_supplierForest_actual_004131
  · exact g32p_supplierForest_actual_004253
  · exact g32p_supplierForest_actual_004261
  · exact g32p_supplierForest_actual_004433
  · exact g32p_supplierForest_actual_004487
  · exact g32p_supplierForest_actual_004590
  · exact g32p_supplierForest_actual_004662
  · exact g32p_supplierForest_actual_004725
  · exact g32p_supplierForest_actual_004761
  · exact g32p_supplierForest_actual_004788
  · exact g32p_supplierForest_actual_004877
  · exact g32p_supplierForest_actual_004895
  · exact g32p_supplierForest_actual_004947
  · exact g32p_supplierForest_actual_004949
  · exact g32p_supplierForest_actual_005055
  · exact g32p_supplierForest_actual_005151
  · exact g32p_supplierForest_actual_005190
  · exact g32p_supplierForest_actual_005220
  · exact g32p_supplierForest_actual_005317
  · exact g32p_supplierForest_actual_005336
  · exact g32p_supplierForest_actual_005462
  · exact g32p_supplierForest_actual_005590
  · exact g32p_supplierForest_actual_005653
  · exact g32p_supplierForest_actual_005709
  · exact g32p_supplierForest_actual_005732
  · exact g32p_supplierForest_actual_005745
  · exact g32p_supplierForest_actual_005751
  · exact g32p_supplierForest_actual_005885
  · exact g32p_supplierForest_actual_005922
  · exact g32p_supplierForest_actual_005977
  · exact g32p_supplierForest_actual_006010
  · exact g32p_supplierForest_actual_006119
  · exact g32p_supplierForest_actual_006225
  · exact g32p_supplierForest_actual_006306
  · exact g32p_supplierForest_actual_006334
  · exact g32p_supplierForest_actual_006355
  · exact g32p_supplierForest_actual_006436
  · exact g32p_supplierForest_actual_006580
  · exact g32p_supplierForest_actual_006585
  · exact g32p_supplierForest_actual_006612
  · exact g32p_supplierForest_actual_006630
  · exact g32p_supplierForest_actual_006649
  · exact g32p_supplierForest_actual_006688
  · exact g32p_supplierForest_actual_006726
  · exact g32p_supplierForest_actual_006745
  · exact g32p_supplierForest_actual_006932
  · exact g32p_supplierForest_actual_006950
  · exact g32p_supplierForest_actual_007099

def g32p_supplierForest_nodes_132 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_007137 else g32p_supplierForest_node_007179) else (if i.val < 3 then g32p_supplierForest_node_007275 else g32p_supplierForest_node_007278)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_007294 else g32p_supplierForest_node_007358) else (if i.val < 7 then g32p_supplierForest_node_007412 else g32p_supplierForest_node_007548))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_007615 else g32p_supplierForest_node_007636) else (if i.val < 11 then g32p_supplierForest_node_007645 else g32p_supplierForest_node_007767)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_007910 else g32p_supplierForest_node_007924) else (if i.val < 15 then g32p_supplierForest_node_007980 else g32p_supplierForest_node_007988)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_008053 else g32p_supplierForest_node_008069) else (if i.val < 19 then g32p_supplierForest_node_008074 else g32p_supplierForest_node_008104)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_008200 else g32p_supplierForest_node_008246) else (if i.val < 23 then g32p_supplierForest_node_008381 else g32p_supplierForest_node_008464))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_008581 else g32p_supplierForest_node_008811) else (if i.val < 27 then g32p_supplierForest_node_008851 else g32p_supplierForest_node_008911)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_008974 else g32p_supplierForest_node_008982) else (if i.val < 31 then g32p_supplierForest_node_009123 else g32p_supplierForest_node_009160))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_009187 else g32p_supplierForest_node_009192) else (if i.val < 35 then g32p_supplierForest_node_009249 else g32p_supplierForest_node_009295)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_009368 else g32p_supplierForest_node_009430) else (if i.val < 39 then g32p_supplierForest_node_009446 else g32p_supplierForest_node_009477))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_009510 else g32p_supplierForest_node_009690) else (if i.val < 43 then g32p_supplierForest_node_009780 else g32p_supplierForest_node_009803)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_009958 else g32p_supplierForest_node_009989) else (if i.val < 47 then g32p_supplierForest_node_009999 else g32p_supplierForest_node_010016)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_010208 else g32p_supplierForest_node_010217) else (if i.val < 51 then g32p_supplierForest_node_010228 else g32p_supplierForest_node_010239)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_010267 else g32p_supplierForest_node_010410) else (if i.val < 55 then g32p_supplierForest_node_010495 else g32p_supplierForest_node_010606))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_010757 else g32p_supplierForest_node_010910) else (if i.val < 59 then g32p_supplierForest_node_010942 else g32p_supplierForest_node_011032)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_011082 else g32p_supplierForest_node_011170) else (if i.val < 63 then g32p_supplierForest_node_011182 else g32p_supplierForest_node_011184)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_011205 else g32p_supplierForest_node_011251) else (if i.val < 67 then g32p_supplierForest_node_011321 else g32p_supplierForest_node_011373)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_011408 else g32p_supplierForest_node_011467) else (if i.val < 71 then g32p_supplierForest_node_011564 else g32p_supplierForest_node_011629))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_011677 else g32p_supplierForest_node_011731) else (if i.val < 75 then g32p_supplierForest_node_011734 else g32p_supplierForest_node_011781)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_011793 else g32p_supplierForest_node_011811) else (if i.val < 79 then g32p_supplierForest_node_011823 else g32p_supplierForest_node_011860)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_011892 else g32p_supplierForest_node_011950) else (if i.val < 83 then g32p_supplierForest_node_012017 else g32p_supplierForest_node_012077)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_012079 else g32p_supplierForest_node_012203) else (if i.val < 87 then g32p_supplierForest_node_012214 else g32p_supplierForest_node_012218))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_012243 else g32p_supplierForest_node_012298) else (if i.val < 91 then g32p_supplierForest_node_012336 else g32p_supplierForest_node_012342)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_012432 else g32p_supplierForest_node_012671) else (if i.val < 95 then g32p_supplierForest_node_012717 else g32p_supplierForest_node_012722))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_012856 else g32p_supplierForest_node_012865) else (if i.val < 99 then g32p_supplierForest_node_012901 else g32p_supplierForest_node_012926)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_012972 else g32p_supplierForest_node_013154) else (if i.val < 103 then g32p_supplierForest_node_013281 else g32p_supplierForest_node_013469))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_013476 else g32p_supplierForest_node_013499) else (if i.val < 107 then g32p_supplierForest_node_013691 else g32p_supplierForest_node_013756)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_013801 else g32p_supplierForest_node_013808) else (if i.val < 111 then g32p_supplierForest_node_013870 else g32p_supplierForest_node_014075)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_014217 else g32p_supplierForest_node_014299) else (if i.val < 115 then g32p_supplierForest_node_014347 else g32p_supplierForest_node_014583)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_014634 else g32p_supplierForest_node_014744) else (if i.val < 119 then g32p_supplierForest_node_015189 else g32p_supplierForest_node_015256))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_015279 else g32p_supplierForest_node_015320) else (if i.val < 123 then g32p_supplierForest_node_015330 else g32p_supplierForest_node_015384)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_015408 else g32p_supplierForest_node_015445) else (if i.val < 127 then g32p_supplierForest_node_015461 else g32p_supplierForest_node_015650))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_015828 else g32p_supplierForest_node_015873) else (if i.val < 131 then g32p_supplierForest_node_015998 else g32p_supplierForest_node_016172)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_016200 else g32p_supplierForest_node_016356) else (if i.val < 135 then g32p_supplierForest_node_016397 else g32p_supplierForest_node_016421))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_016534 else g32p_supplierForest_node_016542) else (if i.val < 139 then g32p_supplierForest_node_016883 else g32p_supplierForest_node_016891)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_016896 else g32p_supplierForest_node_016949) else (if i.val < 143 then g32p_supplierForest_node_017011 else g32p_supplierForest_node_017031)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_017034 else g32p_supplierForest_node_017041) else (if i.val < 147 then g32p_supplierForest_node_017076 else g32p_supplierForest_node_017088)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_017106 else g32p_supplierForest_node_017139) else (if i.val < 151 then g32p_supplierForest_node_017149 else g32p_supplierForest_node_017284))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_017294 else g32p_supplierForest_node_017318) else (if i.val < 155 then g32p_supplierForest_node_017437 else g32p_supplierForest_node_017475)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_017498 else g32p_supplierForest_node_017536) else (if i.val < 159 then g32p_supplierForest_node_017602 else g32p_supplierForest_node_017650))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_017673 else g32p_supplierForest_node_017687) else (if i.val < 163 then g32p_supplierForest_node_017792 else g32p_supplierForest_node_017853)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_017920 else g32p_supplierForest_node_017930) else (if i.val < 167 then g32p_supplierForest_node_017936 else g32p_supplierForest_node_017994))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_018027 else g32p_supplierForest_node_018181) else (if i.val < 171 then g32p_supplierForest_node_018234 else g32p_supplierForest_node_018263)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_018271 else g32p_supplierForest_node_018338) else (if i.val < 175 then g32p_supplierForest_node_018422 else g32p_supplierForest_node_018544)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_018589 else g32p_supplierForest_node_018622) else (if i.val < 179 then g32p_supplierForest_node_018732 else g32p_supplierForest_node_018751)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_018810 else g32p_supplierForest_node_018812) else (if i.val < 183 then g32p_supplierForest_node_018861 else g32p_supplierForest_node_019006))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_019039 else g32p_supplierForest_node_019069) else (if i.val < 187 then g32p_supplierForest_node_019084 else g32p_supplierForest_node_019124)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_019129 else g32p_supplierForest_node_019137) else (if i.val < 191 then g32p_supplierForest_node_019170 else g32p_supplierForest_node_019346)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_019370 else g32p_supplierForest_node_019373) else (if i.val < 195 then g32p_supplierForest_node_019492 else g32p_supplierForest_node_019551)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_019634 else g32p_supplierForest_node_019648) else (if i.val < 199 then g32p_supplierForest_node_019764 else g32p_supplierForest_node_019887))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_019901 else g32p_supplierForest_node_019948) else (if i.val < 203 then g32p_supplierForest_node_020042 else g32p_supplierForest_node_020128)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_020243 else g32p_supplierForest_node_020269) else (if i.val < 207 then g32p_supplierForest_node_020279 else g32p_supplierForest_node_020303)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_020306 else g32p_supplierForest_node_020450) else (if i.val < 211 then g32p_supplierForest_node_020559 else g32p_supplierForest_node_020599)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_020630 else g32p_supplierForest_node_020718) else (if i.val < 215 then g32p_supplierForest_node_020745 else g32p_supplierForest_node_020764))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_020787 else g32p_supplierForest_node_020849) else (if i.val < 219 then g32p_supplierForest_node_020852 else g32p_supplierForest_node_020915)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_020929 else g32p_supplierForest_node_020936) else (if i.val < 223 then g32p_supplierForest_node_021031 else g32p_supplierForest_node_021068))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_021220 else g32p_supplierForest_node_021371) else (if i.val < 227 then g32p_supplierForest_node_021416 else g32p_supplierForest_node_021438)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_021566 else g32p_supplierForest_node_021645) else (if i.val < 231 then g32p_supplierForest_node_021674 else g32p_supplierForest_node_021759))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_021841 else g32p_supplierForest_node_021864) else (if i.val < 235 then g32p_supplierForest_node_021876 else g32p_supplierForest_node_021880)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_021928 else g32p_supplierForest_node_021991) else (if i.val < 239 then g32p_supplierForest_node_022039 else g32p_supplierForest_node_022049)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_022087 else g32p_supplierForest_node_022113) else (if i.val < 243 then g32p_supplierForest_node_022158 else g32p_supplierForest_node_022163)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_022250 else g32p_supplierForest_node_022266) else (if i.val < 247 then g32p_supplierForest_node_022320 else g32p_supplierForest_node_022370))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_022404 else g32p_supplierForest_node_022511) else (if i.val < 251 then g32p_supplierForest_node_022581 else g32p_supplierForest_node_022621)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_022631 else g32p_supplierForest_node_022661) else (if i.val < 255 then g32p_supplierForest_node_022679 else g32p_supplierForest_node_022688))))))))

def g32p_supplierForest_classes_132 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 21 else 22) else (if i.val < 3 then 22 else 40)) else (if i.val < 6 then (if i.val < 5 then 39 else 39) else (if i.val < 7 then 38 else 38))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 21) else (if i.val < 11 then 39 else 21)) else (if i.val < 14 then (if i.val < 13 then 7 else 22) else (if i.val < 15 then 38 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 38) else (if i.val < 19 then 22 else 7)) else (if i.val < 22 then (if i.val < 21 then 21 else 38) else (if i.val < 23 then 38 else 38))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 38 else 38) else (if i.val < 27 then 22 else 22)) else (if i.val < 30 then (if i.val < 29 then 21 else 22) else (if i.val < 31 then 38 else 21))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 38) else (if i.val < 35 then 38 else 38)) else (if i.val < 38 then (if i.val < 37 then 7 else 22) else (if i.val < 39 then 38 else 22))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 38) else (if i.val < 43 then 22 else 21)) else (if i.val < 46 then (if i.val < 45 then 40 else 38) else (if i.val < 47 then 40 else 7)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 7 else 22) else (if i.val < 51 then 38 else 21)) else (if i.val < 54 then (if i.val < 53 then 7 else 21) else (if i.val < 55 then 38 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 43 else 38) else (if i.val < 59 then 21 else 21)) else (if i.val < 62 then (if i.val < 61 then 20 else 21) else (if i.val < 63 then 21 else 43)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 21 else 22) else (if i.val < 67 then 22 else 38)) else (if i.val < 70 then (if i.val < 69 then 39 else 7) else (if i.val < 71 then 22 else 43))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 38 else 38) else (if i.val < 75 then 21 else 38)) else (if i.val < 78 then (if i.val < 77 then 7 else 38) else (if i.val < 79 then 38 else 38)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 40 else 38) else (if i.val < 83 then 38 else 38)) else (if i.val < 86 then (if i.val < 85 then 22 else 20) else (if i.val < 87 then 22 else 21))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 40 else 38) else (if i.val < 91 then 25 else 25)) else (if i.val < 94 then (if i.val < 93 then 26 else 26) else (if i.val < 95 then 49 else 26))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 49 else 46) else (if i.val < 99 then 10 else 46)) else (if i.val < 102 then (if i.val < 101 then 49 else 10) else (if i.val < 103 then 9 else 49))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 49 else 50) else (if i.val < 107 then 10 else 49)) else (if i.val < 110 then (if i.val < 109 then 50 else 49) else (if i.val < 111 then 25 else 45)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 26 else 49) else (if i.val < 115 then 48 else 12)) else (if i.val < 118 then (if i.val < 117 then 50 else 50) else (if i.val < 119 then 10 else 47))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 49 else 9) else (if i.val < 123 then 49 else 49)) else (if i.val < 126 then (if i.val < 125 then 50 else 26) else (if i.val < 127 then 25 else 49))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 47 else 10) else (if i.val < 131 then 26 else 49)) else (if i.val < 134 then (if i.val < 133 then 49 else 9) else (if i.val < 135 then 48 else 49))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 47 else 49) else (if i.val < 139 then 45 else 25)) else (if i.val < 142 then (if i.val < 141 then 49 else 46) else (if i.val < 143 then 12 else 50)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 48 else 50) else (if i.val < 147 then 25 else 47)) else (if i.val < 150 then (if i.val < 149 then 50 else 49) else (if i.val < 151 then 25 else 10))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 49 else 25) else (if i.val < 155 then 47 else 49)) else (if i.val < 158 then (if i.val < 157 then 49 else 47) else (if i.val < 159 then 26 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 50 else 26) else (if i.val < 163 then 49 else 49)) else (if i.val < 166 then (if i.val < 165 then 49 else 46) else (if i.val < 167 then 49 else 49))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 27) else (if i.val < 171 then 49 else 26)) else (if i.val < 174 then (if i.val < 173 then 47 else 49) else (if i.val < 175 then 49 else 49)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 27 else 47) else (if i.val < 179 then 12 else 47)) else (if i.val < 182 then (if i.val < 181 then 9 else 12) else (if i.val < 183 then 49 else 46))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 9 else 26) else (if i.val < 187 then 25 else 49)) else (if i.val < 190 then (if i.val < 189 then 49 else 46) else (if i.val < 191 then 49 else 9)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 49 else 49) else (if i.val < 195 then 25 else 46)) else (if i.val < 198 then (if i.val < 197 then 46 else 10) else (if i.val < 199 then 46 else 46))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 25 else 12) else (if i.val < 203 then 52 else 25)) else (if i.val < 206 then (if i.val < 205 then 46 else 52) else (if i.val < 207 then 50 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 26 else 47) else (if i.val < 211 then 49 else 9)) else (if i.val < 214 then (if i.val < 213 then 49 else 49) else (if i.val < 215 then 12 else 46))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 26 else 47) else (if i.val < 219 then 49 else 10)) else (if i.val < 222 then (if i.val < 221 then 12 else 49) else (if i.val < 223 then 49 else 47))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 12 else 49) else (if i.val < 227 then 49 else 49)) else (if i.val < 230 then (if i.val < 229 then 12 else 49) else (if i.val < 231 then 48 else 10))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 27 else 46) else (if i.val < 235 then 49 else 26)) else (if i.val < 238 then (if i.val < 237 then 47 else 49) else (if i.val < 239 then 50 else 25)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 49) else (if i.val < 243 then 49 else 49)) else (if i.val < 246 then (if i.val < 245 then 49 else 49) else (if i.val < 247 then 49 else 27))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 26 else 26) else (if i.val < 251 then 26 else 49)) else (if i.val < 254 then (if i.val < 253 then 26 else 46) else (if i.val < 255 then 47 else 47))))))))

theorem g32p_supplierForest_actual_132 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_132 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_132 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_007137
  · exact g32p_supplierForest_actual_007179
  · exact g32p_supplierForest_actual_007275
  · exact g32p_supplierForest_actual_007278
  · exact g32p_supplierForest_actual_007294
  · exact g32p_supplierForest_actual_007358
  · exact g32p_supplierForest_actual_007412
  · exact g32p_supplierForest_actual_007548
  · exact g32p_supplierForest_actual_007615
  · exact g32p_supplierForest_actual_007636
  · exact g32p_supplierForest_actual_007645
  · exact g32p_supplierForest_actual_007767
  · exact g32p_supplierForest_actual_007910
  · exact g32p_supplierForest_actual_007924
  · exact g32p_supplierForest_actual_007980
  · exact g32p_supplierForest_actual_007988
  · exact g32p_supplierForest_actual_008053
  · exact g32p_supplierForest_actual_008069
  · exact g32p_supplierForest_actual_008074
  · exact g32p_supplierForest_actual_008104
  · exact g32p_supplierForest_actual_008200
  · exact g32p_supplierForest_actual_008246
  · exact g32p_supplierForest_actual_008381
  · exact g32p_supplierForest_actual_008464
  · exact g32p_supplierForest_actual_008581
  · exact g32p_supplierForest_actual_008811
  · exact g32p_supplierForest_actual_008851
  · exact g32p_supplierForest_actual_008911
  · exact g32p_supplierForest_actual_008974
  · exact g32p_supplierForest_actual_008982
  · exact g32p_supplierForest_actual_009123
  · exact g32p_supplierForest_actual_009160
  · exact g32p_supplierForest_actual_009187
  · exact g32p_supplierForest_actual_009192
  · exact g32p_supplierForest_actual_009249
  · exact g32p_supplierForest_actual_009295
  · exact g32p_supplierForest_actual_009368
  · exact g32p_supplierForest_actual_009430
  · exact g32p_supplierForest_actual_009446
  · exact g32p_supplierForest_actual_009477
  · exact g32p_supplierForest_actual_009510
  · exact g32p_supplierForest_actual_009690
  · exact g32p_supplierForest_actual_009780
  · exact g32p_supplierForest_actual_009803
  · exact g32p_supplierForest_actual_009958
  · exact g32p_supplierForest_actual_009989
  · exact g32p_supplierForest_actual_009999
  · exact g32p_supplierForest_actual_010016
  · exact g32p_supplierForest_actual_010208
  · exact g32p_supplierForest_actual_010217
  · exact g32p_supplierForest_actual_010228
  · exact g32p_supplierForest_actual_010239
  · exact g32p_supplierForest_actual_010267
  · exact g32p_supplierForest_actual_010410
  · exact g32p_supplierForest_actual_010495
  · exact g32p_supplierForest_actual_010606
  · exact g32p_supplierForest_actual_010757
  · exact g32p_supplierForest_actual_010910
  · exact g32p_supplierForest_actual_010942
  · exact g32p_supplierForest_actual_011032
  · exact g32p_supplierForest_actual_011082
  · exact g32p_supplierForest_actual_011170
  · exact g32p_supplierForest_actual_011182
  · exact g32p_supplierForest_actual_011184
  · exact g32p_supplierForest_actual_011205
  · exact g32p_supplierForest_actual_011251
  · exact g32p_supplierForest_actual_011321
  · exact g32p_supplierForest_actual_011373
  · exact g32p_supplierForest_actual_011408
  · exact g32p_supplierForest_actual_011467
  · exact g32p_supplierForest_actual_011564
  · exact g32p_supplierForest_actual_011629
  · exact g32p_supplierForest_actual_011677
  · exact g32p_supplierForest_actual_011731
  · exact g32p_supplierForest_actual_011734
  · exact g32p_supplierForest_actual_011781
  · exact g32p_supplierForest_actual_011793
  · exact g32p_supplierForest_actual_011811
  · exact g32p_supplierForest_actual_011823
  · exact g32p_supplierForest_actual_011860
  · exact g32p_supplierForest_actual_011892
  · exact g32p_supplierForest_actual_011950
  · exact g32p_supplierForest_actual_012017
  · exact g32p_supplierForest_actual_012077
  · exact g32p_supplierForest_actual_012079
  · exact g32p_supplierForest_actual_012203
  · exact g32p_supplierForest_actual_012214
  · exact g32p_supplierForest_actual_012218
  · exact g32p_supplierForest_actual_012243
  · exact g32p_supplierForest_actual_012298
  · exact g32p_supplierForest_actual_012336
  · exact g32p_supplierForest_actual_012342
  · exact g32p_supplierForest_actual_012432
  · exact g32p_supplierForest_actual_012671
  · exact g32p_supplierForest_actual_012717
  · exact g32p_supplierForest_actual_012722
  · exact g32p_supplierForest_actual_012856
  · exact g32p_supplierForest_actual_012865
  · exact g32p_supplierForest_actual_012901
  · exact g32p_supplierForest_actual_012926
  · exact g32p_supplierForest_actual_012972
  · exact g32p_supplierForest_actual_013154
  · exact g32p_supplierForest_actual_013281
  · exact g32p_supplierForest_actual_013469
  · exact g32p_supplierForest_actual_013476
  · exact g32p_supplierForest_actual_013499
  · exact g32p_supplierForest_actual_013691
  · exact g32p_supplierForest_actual_013756
  · exact g32p_supplierForest_actual_013801
  · exact g32p_supplierForest_actual_013808
  · exact g32p_supplierForest_actual_013870
  · exact g32p_supplierForest_actual_014075
  · exact g32p_supplierForest_actual_014217
  · exact g32p_supplierForest_actual_014299
  · exact g32p_supplierForest_actual_014347
  · exact g32p_supplierForest_actual_014583
  · exact g32p_supplierForest_actual_014634
  · exact g32p_supplierForest_actual_014744
  · exact g32p_supplierForest_actual_015189
  · exact g32p_supplierForest_actual_015256
  · exact g32p_supplierForest_actual_015279
  · exact g32p_supplierForest_actual_015320
  · exact g32p_supplierForest_actual_015330
  · exact g32p_supplierForest_actual_015384
  · exact g32p_supplierForest_actual_015408
  · exact g32p_supplierForest_actual_015445
  · exact g32p_supplierForest_actual_015461
  · exact g32p_supplierForest_actual_015650
  · exact g32p_supplierForest_actual_015828
  · exact g32p_supplierForest_actual_015873
  · exact g32p_supplierForest_actual_015998
  · exact g32p_supplierForest_actual_016172
  · exact g32p_supplierForest_actual_016200
  · exact g32p_supplierForest_actual_016356
  · exact g32p_supplierForest_actual_016397
  · exact g32p_supplierForest_actual_016421
  · exact g32p_supplierForest_actual_016534
  · exact g32p_supplierForest_actual_016542
  · exact g32p_supplierForest_actual_016883
  · exact g32p_supplierForest_actual_016891
  · exact g32p_supplierForest_actual_016896
  · exact g32p_supplierForest_actual_016949
  · exact g32p_supplierForest_actual_017011
  · exact g32p_supplierForest_actual_017031
  · exact g32p_supplierForest_actual_017034
  · exact g32p_supplierForest_actual_017041
  · exact g32p_supplierForest_actual_017076
  · exact g32p_supplierForest_actual_017088
  · exact g32p_supplierForest_actual_017106
  · exact g32p_supplierForest_actual_017139
  · exact g32p_supplierForest_actual_017149
  · exact g32p_supplierForest_actual_017284
  · exact g32p_supplierForest_actual_017294
  · exact g32p_supplierForest_actual_017318
  · exact g32p_supplierForest_actual_017437
  · exact g32p_supplierForest_actual_017475
  · exact g32p_supplierForest_actual_017498
  · exact g32p_supplierForest_actual_017536
  · exact g32p_supplierForest_actual_017602
  · exact g32p_supplierForest_actual_017650
  · exact g32p_supplierForest_actual_017673
  · exact g32p_supplierForest_actual_017687
  · exact g32p_supplierForest_actual_017792
  · exact g32p_supplierForest_actual_017853
  · exact g32p_supplierForest_actual_017920
  · exact g32p_supplierForest_actual_017930
  · exact g32p_supplierForest_actual_017936
  · exact g32p_supplierForest_actual_017994
  · exact g32p_supplierForest_actual_018027
  · exact g32p_supplierForest_actual_018181
  · exact g32p_supplierForest_actual_018234
  · exact g32p_supplierForest_actual_018263
  · exact g32p_supplierForest_actual_018271
  · exact g32p_supplierForest_actual_018338
  · exact g32p_supplierForest_actual_018422
  · exact g32p_supplierForest_actual_018544
  · exact g32p_supplierForest_actual_018589
  · exact g32p_supplierForest_actual_018622
  · exact g32p_supplierForest_actual_018732
  · exact g32p_supplierForest_actual_018751
  · exact g32p_supplierForest_actual_018810
  · exact g32p_supplierForest_actual_018812
  · exact g32p_supplierForest_actual_018861
  · exact g32p_supplierForest_actual_019006
  · exact g32p_supplierForest_actual_019039
  · exact g32p_supplierForest_actual_019069
  · exact g32p_supplierForest_actual_019084
  · exact g32p_supplierForest_actual_019124
  · exact g32p_supplierForest_actual_019129
  · exact g32p_supplierForest_actual_019137
  · exact g32p_supplierForest_actual_019170
  · exact g32p_supplierForest_actual_019346
  · exact g32p_supplierForest_actual_019370
  · exact g32p_supplierForest_actual_019373
  · exact g32p_supplierForest_actual_019492
  · exact g32p_supplierForest_actual_019551
  · exact g32p_supplierForest_actual_019634
  · exact g32p_supplierForest_actual_019648
  · exact g32p_supplierForest_actual_019764
  · exact g32p_supplierForest_actual_019887
  · exact g32p_supplierForest_actual_019901
  · exact g32p_supplierForest_actual_019948
  · exact g32p_supplierForest_actual_020042
  · exact g32p_supplierForest_actual_020128
  · exact g32p_supplierForest_actual_020243
  · exact g32p_supplierForest_actual_020269
  · exact g32p_supplierForest_actual_020279
  · exact g32p_supplierForest_actual_020303
  · exact g32p_supplierForest_actual_020306
  · exact g32p_supplierForest_actual_020450
  · exact g32p_supplierForest_actual_020559
  · exact g32p_supplierForest_actual_020599
  · exact g32p_supplierForest_actual_020630
  · exact g32p_supplierForest_actual_020718
  · exact g32p_supplierForest_actual_020745
  · exact g32p_supplierForest_actual_020764
  · exact g32p_supplierForest_actual_020787
  · exact g32p_supplierForest_actual_020849
  · exact g32p_supplierForest_actual_020852
  · exact g32p_supplierForest_actual_020915
  · exact g32p_supplierForest_actual_020929
  · exact g32p_supplierForest_actual_020936
  · exact g32p_supplierForest_actual_021031
  · exact g32p_supplierForest_actual_021068
  · exact g32p_supplierForest_actual_021220
  · exact g32p_supplierForest_actual_021371
  · exact g32p_supplierForest_actual_021416
  · exact g32p_supplierForest_actual_021438
  · exact g32p_supplierForest_actual_021566
  · exact g32p_supplierForest_actual_021645
  · exact g32p_supplierForest_actual_021674
  · exact g32p_supplierForest_actual_021759
  · exact g32p_supplierForest_actual_021841
  · exact g32p_supplierForest_actual_021864
  · exact g32p_supplierForest_actual_021876
  · exact g32p_supplierForest_actual_021880
  · exact g32p_supplierForest_actual_021928
  · exact g32p_supplierForest_actual_021991
  · exact g32p_supplierForest_actual_022039
  · exact g32p_supplierForest_actual_022049
  · exact g32p_supplierForest_actual_022087
  · exact g32p_supplierForest_actual_022113
  · exact g32p_supplierForest_actual_022158
  · exact g32p_supplierForest_actual_022163
  · exact g32p_supplierForest_actual_022250
  · exact g32p_supplierForest_actual_022266
  · exact g32p_supplierForest_actual_022320
  · exact g32p_supplierForest_actual_022370
  · exact g32p_supplierForest_actual_022404
  · exact g32p_supplierForest_actual_022511
  · exact g32p_supplierForest_actual_022581
  · exact g32p_supplierForest_actual_022621
  · exact g32p_supplierForest_actual_022631
  · exact g32p_supplierForest_actual_022661
  · exact g32p_supplierForest_actual_022679
  · exact g32p_supplierForest_actual_022688

def g32p_supplierForest_nodes_133 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_022690 else g32p_supplierForest_node_022859) else (if i.val < 3 then g32p_supplierForest_node_022936 else g32p_supplierForest_node_022955)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_023173 else g32p_supplierForest_node_023207) else (if i.val < 7 then g32p_supplierForest_node_023308 else g32p_supplierForest_node_023363))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_023365 else g32p_supplierForest_node_023440) else (if i.val < 11 then g32p_supplierForest_node_023465 else g32p_supplierForest_node_023603)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_023627 else g32p_supplierForest_node_023636) else (if i.val < 15 then g32p_supplierForest_node_023670 else g32p_supplierForest_node_023748)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_023751 else g32p_supplierForest_node_023839) else (if i.val < 19 then g32p_supplierForest_node_023883 else g32p_supplierForest_node_023890)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_023919 else g32p_supplierForest_node_023947) else (if i.val < 23 then g32p_supplierForest_node_024116 else g32p_supplierForest_node_024136))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_024137 else g32p_supplierForest_node_024301) else (if i.val < 27 then g32p_supplierForest_node_024339 else g32p_supplierForest_node_024386)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_024471 else g32p_supplierForest_node_024473) else (if i.val < 31 then g32p_supplierForest_node_024526 else g32p_supplierForest_node_024571))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_024656 else g32p_supplierForest_node_024714) else (if i.val < 35 then g32p_supplierForest_node_024756 else g32p_supplierForest_node_024821)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_024825 else g32p_supplierForest_node_024839) else (if i.val < 39 then g32p_supplierForest_node_024880 else g32p_supplierForest_node_024935))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_024999 else g32p_supplierForest_node_025020) else (if i.val < 43 then g32p_supplierForest_node_025228 else g32p_supplierForest_node_025360)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_025417 else g32p_supplierForest_node_025537) else (if i.val < 47 then g32p_supplierForest_node_025651 else g32p_supplierForest_node_025708)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_025876 else g32p_supplierForest_node_025880) else (if i.val < 51 then g32p_supplierForest_node_025913 else g32p_supplierForest_node_026015)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_026148 else g32p_supplierForest_node_026171) else (if i.val < 55 then g32p_supplierForest_node_026269 else g32p_supplierForest_node_026479))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_026532 else g32p_supplierForest_node_026535) else (if i.val < 59 then g32p_supplierForest_node_026554 else g32p_supplierForest_node_026570)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_026636 else g32p_supplierForest_node_026650) else (if i.val < 63 then g32p_supplierForest_node_026694 else g32p_supplierForest_node_026709)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_026727 else g32p_supplierForest_node_026770) else (if i.val < 67 then g32p_supplierForest_node_026781 else g32p_supplierForest_node_026792)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_026819 else g32p_supplierForest_node_026840) else (if i.val < 71 then g32p_supplierForest_node_026860 else g32p_supplierForest_node_026896))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_026938 else g32p_supplierForest_node_026957) else (if i.val < 75 then g32p_supplierForest_node_026964 else g32p_supplierForest_node_027001)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_027059 else g32p_supplierForest_node_027179) else (if i.val < 79 then g32p_supplierForest_node_027201 else g32p_supplierForest_node_027238)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_027272 else g32p_supplierForest_node_027298) else (if i.val < 83 then g32p_supplierForest_node_027301 else g32p_supplierForest_node_027317)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_027349 else g32p_supplierForest_node_027381) else (if i.val < 87 then g32p_supplierForest_node_027396 else g32p_supplierForest_node_027470))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_027510 else g32p_supplierForest_node_027530) else (if i.val < 91 then g32p_supplierForest_node_027538 else g32p_supplierForest_node_027562)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_027677 else g32p_supplierForest_node_027746) else (if i.val < 95 then g32p_supplierForest_node_027772 else g32p_supplierForest_node_027872))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_027879 else g32p_supplierForest_node_027898) else (if i.val < 99 then g32p_supplierForest_node_027913 else g32p_supplierForest_node_027977)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_028017 else g32p_supplierForest_node_028057) else (if i.val < 103 then g32p_supplierForest_node_028165 else g32p_supplierForest_node_028198))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_028577 else g32p_supplierForest_node_028588) else (if i.val < 107 then g32p_supplierForest_node_028868 else g32p_supplierForest_node_028871)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_029089 else g32p_supplierForest_node_029108) else (if i.val < 111 then g32p_supplierForest_node_029136 else g32p_supplierForest_node_029149)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_029379 else g32p_supplierForest_node_029412) else (if i.val < 115 then g32p_supplierForest_node_029443 else g32p_supplierForest_node_029490)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_029584 else g32p_supplierForest_node_029628) else (if i.val < 119 then g32p_supplierForest_node_029645 else g32p_supplierForest_node_029664))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_029696 else g32p_supplierForest_node_029731) else (if i.val < 123 then g32p_supplierForest_node_029838 else g32p_supplierForest_node_029911)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_029915 else g32p_supplierForest_node_029943) else (if i.val < 127 then g32p_supplierForest_node_030011 else g32p_supplierForest_node_030039))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_030041 else g32p_supplierForest_node_030124) else (if i.val < 131 then g32p_supplierForest_node_030210 else g32p_supplierForest_node_030358)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_030389 else g32p_supplierForest_node_030441) else (if i.val < 135 then g32p_supplierForest_node_030452 else g32p_supplierForest_node_030535))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_030591 else g32p_supplierForest_node_030695) else (if i.val < 139 then g32p_supplierForest_node_030717 else g32p_supplierForest_node_030886)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_030910 else g32p_supplierForest_node_030912) else (if i.val < 143 then g32p_supplierForest_node_030976 else g32p_supplierForest_node_031167)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_031243 else g32p_supplierForest_node_031298) else (if i.val < 147 then g32p_supplierForest_node_031310 else g32p_supplierForest_node_031428)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_031562 else g32p_supplierForest_node_031618) else (if i.val < 151 then g32p_supplierForest_node_031676 else g32p_supplierForest_node_031700))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_031719 else g32p_supplierForest_node_031721) else (if i.val < 155 then g32p_supplierForest_node_031932 else g32p_supplierForest_node_031959)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_031983 else g32p_supplierForest_node_032065) else (if i.val < 159 then g32p_supplierForest_node_032089 else g32p_supplierForest_node_032226))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_032240 else g32p_supplierForest_node_032242) else (if i.val < 163 then g32p_supplierForest_node_032273 else g32p_supplierForest_node_032351)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_032405 else g32p_supplierForest_node_032453) else (if i.val < 167 then g32p_supplierForest_node_032538 else g32p_supplierForest_node_032667))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_032708 else g32p_supplierForest_node_032824) else (if i.val < 171 then g32p_supplierForest_node_032918 else g32p_supplierForest_node_032929)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_033014 else g32p_supplierForest_node_033132) else (if i.val < 175 then g32p_supplierForest_node_033147 else g32p_supplierForest_node_033194)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_033198 else g32p_supplierForest_node_033205) else (if i.val < 179 then g32p_supplierForest_node_033265 else g32p_supplierForest_node_033280)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_033354 else g32p_supplierForest_node_033459) else (if i.val < 183 then g32p_supplierForest_node_033537 else g32p_supplierForest_node_033584))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_033608 else g32p_supplierForest_node_033965) else (if i.val < 187 then g32p_supplierForest_node_034004 else g32p_supplierForest_node_034019)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_034173 else g32p_supplierForest_node_034225) else (if i.val < 191 then g32p_supplierForest_node_034234 else g32p_supplierForest_node_034448)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_034481 else g32p_supplierForest_node_034629) else (if i.val < 195 then g32p_supplierForest_node_034756 else g32p_supplierForest_node_034945)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_034955 else g32p_supplierForest_node_035068) else (if i.val < 199 then g32p_supplierForest_node_035071 else g32p_supplierForest_node_035165))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_035219 else g32p_supplierForest_node_035275) else (if i.val < 203 then g32p_supplierForest_node_035421 else g32p_supplierForest_node_035444)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_035480 else g32p_supplierForest_node_035533) else (if i.val < 207 then g32p_supplierForest_node_035543 else g32p_supplierForest_node_035544)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_035555 else g32p_supplierForest_node_035576) else (if i.val < 211 then g32p_supplierForest_node_035685 else g32p_supplierForest_node_035707)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_036016 else g32p_supplierForest_node_036022) else (if i.val < 215 then g32p_supplierForest_node_036030 else g32p_supplierForest_node_036059))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_036071 else g32p_supplierForest_node_036105) else (if i.val < 219 then g32p_supplierForest_node_036164 else g32p_supplierForest_node_036167)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_036191 else g32p_supplierForest_node_036223) else (if i.val < 223 then g32p_supplierForest_node_036264 else g32p_supplierForest_node_036268))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_036317 else g32p_supplierForest_node_036318) else (if i.val < 227 then g32p_supplierForest_node_036341 else g32p_supplierForest_node_036485)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_036537 else g32p_supplierForest_node_036607) else (if i.val < 231 then g32p_supplierForest_node_036685 else g32p_supplierForest_node_036705))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_036731 else g32p_supplierForest_node_036748) else (if i.val < 235 then g32p_supplierForest_node_036768 else g32p_supplierForest_node_036807)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_036890 else g32p_supplierForest_node_036944) else (if i.val < 239 then g32p_supplierForest_node_036967 else g32p_supplierForest_node_037054)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_037055 else g32p_supplierForest_node_037125) else (if i.val < 243 then g32p_supplierForest_node_037135 else g32p_supplierForest_node_037149)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_037202 else g32p_supplierForest_node_037275) else (if i.val < 247 then g32p_supplierForest_node_037397 else g32p_supplierForest_node_037457))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_037475 else g32p_supplierForest_node_037482) else (if i.val < 251 then g32p_supplierForest_node_037541 else g32p_supplierForest_node_037556)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_037594 else g32p_supplierForest_node_037616) else (if i.val < 255 then g32p_supplierForest_node_037632 else g32p_supplierForest_node_037635))))))))

def g32p_supplierForest_classes_133 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 26 else 26) else (if i.val < 3 then 49 else 47)) else (if i.val < 6 then (if i.val < 5 then 49 else 49) else (if i.val < 7 then 26 else 48))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 46) else (if i.val < 11 then 26 else 49)) else (if i.val < 14 then (if i.val < 13 then 45 else 46) else (if i.val < 15 then 49 else 47)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 26 else 47) else (if i.val < 19 then 46 else 49)) else (if i.val < 22 then (if i.val < 21 then 49 else 49) else (if i.val < 23 then 49 else 50))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 12) else (if i.val < 27 then 9 else 46)) else (if i.val < 30 then (if i.val < 29 then 49 else 46) else (if i.val < 31 then 29 else 33))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 16 else 30) else (if i.val < 35 then 30 else 30)) else (if i.val < 38 then (if i.val < 37 then 17 else 30) else (if i.val < 39 then 16 else 29))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 16 else 15) else (if i.val < 43 then 15 else 57)) else (if i.val < 46 then (if i.val < 45 then 57 else 57) else (if i.val < 47 then 57 else 60)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 30 else 57) else (if i.val < 51 then 62 else 30)) else (if i.val < 54 then (if i.val < 53 then 30 else 14) else (if i.val < 55 then 57 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 29 else 36) else (if i.val < 59 then 30 else 57)) else (if i.val < 62 then (if i.val < 61 then 57 else 58) else (if i.val < 63 then 57 else 58)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 16 else 57) else (if i.val < 67 then 59 else 57)) else (if i.val < 70 then (if i.val < 69 then 33 else 16) else (if i.val < 71 then 16 else 32))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 57 else 29) else (if i.val < 75 then 16 else 15)) else (if i.val < 78 then (if i.val < 77 then 30 else 57) else (if i.val < 79 then 16 else 57)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 16 else 57) else (if i.val < 83 then 29 else 62)) else (if i.val < 86 then (if i.val < 85 then 57 else 16) else (if i.val < 87 then 30 else 30))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 16) else (if i.val < 91 then 16 else 60)) else (if i.val < 94 then (if i.val < 93 then 57 else 36) else (if i.val < 95 then 57 else 16))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 30 else 16) else (if i.val < 99 then 17 else 16)) else (if i.val < 102 then (if i.val < 101 then 33 else 57) else (if i.val < 103 then 60 else 57))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 16 else 30) else (if i.val < 107 then 30 else 30)) else (if i.val < 110 then (if i.val < 109 then 16 else 57) else (if i.val < 111 then 57 else 30)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 57 else 57) else (if i.val < 115 then 57 else 29)) else (if i.val < 118 then (if i.val < 117 then 57 else 57) else (if i.val < 119 then 16 else 60))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 60 else 30) else (if i.val < 123 then 57 else 57)) else (if i.val < 126 then (if i.val < 125 then 30 else 30) else (if i.val < 127 then 16 else 30))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 30 else 36) else (if i.val < 131 then 57 else 30)) else (if i.val < 134 then (if i.val < 133 then 57 else 30) else (if i.val < 135 then 14 else 30))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 57 else 60) else (if i.val < 139 then 57 else 57)) else (if i.val < 142 then (if i.val < 141 then 57 else 30) else (if i.val < 143 then 30 else 30)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 57 else 30) else (if i.val < 147 then 57 else 16)) else (if i.val < 150 then (if i.val < 149 then 16 else 30) else (if i.val < 151 then 57 else 30))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 62 else 57) else (if i.val < 155 then 16 else 57)) else (if i.val < 158 then (if i.val < 157 then 57 else 63) else (if i.val < 159 then 57 else 57))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 57 else 16) else (if i.val < 163 then 57 else 57)) else (if i.val < 166 then (if i.val < 165 then 29 else 57) else (if i.val < 167 then 35 else 30))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 57 else 30) else (if i.val < 171 then 36 else 30)) else (if i.val < 174 then (if i.val < 173 then 57 else 17) else (if i.val < 175 then 30 else 58)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 30 else 57) else (if i.val < 179 then 16 else 30)) else (if i.val < 182 then (if i.val < 181 then 57 else 15) else (if i.val < 183 then 57 else 57))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 29 else 57) else (if i.val < 187 then 30 else 30)) else (if i.val < 190 then (if i.val < 189 then 59 else 57) else (if i.val < 191 then 63 else 57)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 29 else 30) else (if i.val < 195 then 30 else 57)) else (if i.val < 198 then (if i.val < 197 then 36 else 57) else (if i.val < 199 then 57 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 57 else 30) else (if i.val < 203 then 29 else 57)) else (if i.val < 206 then (if i.val < 205 then 57 else 33) else (if i.val < 207 then 30 else 30)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 30 else 57) else (if i.val < 211 then 57 else 57)) else (if i.val < 214 then (if i.val < 213 then 30 else 16) else (if i.val < 215 then 16 else 16))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 62 else 62) else (if i.val < 219 then 16 else 30)) else (if i.val < 222 then (if i.val < 221 then 16 else 36) else (if i.val < 223 then 57 else 59))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 57 else 16) else (if i.val < 227 then 57 else 57)) else (if i.val < 230 then (if i.val < 229 then 30 else 57) else (if i.val < 231 then 57 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 16) else (if i.val < 235 then 15 else 30)) else (if i.val < 238 then (if i.val < 237 then 16 else 59) else (if i.val < 239 then 17 else 36)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 30 else 30) else (if i.val < 243 then 17 else 57)) else (if i.val < 246 then (if i.val < 245 then 15 else 16) else (if i.val < 247 then 57 else 57))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 15 else 14) else (if i.val < 251 then 17 else 59)) else (if i.val < 254 then (if i.val < 253 then 35 else 57) else (if i.val < 255 then 57 else 29))))))))

theorem g32p_supplierForest_actual_133 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_133 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_133 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_022690
  · exact g32p_supplierForest_actual_022859
  · exact g32p_supplierForest_actual_022936
  · exact g32p_supplierForest_actual_022955
  · exact g32p_supplierForest_actual_023173
  · exact g32p_supplierForest_actual_023207
  · exact g32p_supplierForest_actual_023308
  · exact g32p_supplierForest_actual_023363
  · exact g32p_supplierForest_actual_023365
  · exact g32p_supplierForest_actual_023440
  · exact g32p_supplierForest_actual_023465
  · exact g32p_supplierForest_actual_023603
  · exact g32p_supplierForest_actual_023627
  · exact g32p_supplierForest_actual_023636
  · exact g32p_supplierForest_actual_023670
  · exact g32p_supplierForest_actual_023748
  · exact g32p_supplierForest_actual_023751
  · exact g32p_supplierForest_actual_023839
  · exact g32p_supplierForest_actual_023883
  · exact g32p_supplierForest_actual_023890
  · exact g32p_supplierForest_actual_023919
  · exact g32p_supplierForest_actual_023947
  · exact g32p_supplierForest_actual_024116
  · exact g32p_supplierForest_actual_024136
  · exact g32p_supplierForest_actual_024137
  · exact g32p_supplierForest_actual_024301
  · exact g32p_supplierForest_actual_024339
  · exact g32p_supplierForest_actual_024386
  · exact g32p_supplierForest_actual_024471
  · exact g32p_supplierForest_actual_024473
  · exact g32p_supplierForest_actual_024526
  · exact g32p_supplierForest_actual_024571
  · exact g32p_supplierForest_actual_024656
  · exact g32p_supplierForest_actual_024714
  · exact g32p_supplierForest_actual_024756
  · exact g32p_supplierForest_actual_024821
  · exact g32p_supplierForest_actual_024825
  · exact g32p_supplierForest_actual_024839
  · exact g32p_supplierForest_actual_024880
  · exact g32p_supplierForest_actual_024935
  · exact g32p_supplierForest_actual_024999
  · exact g32p_supplierForest_actual_025020
  · exact g32p_supplierForest_actual_025228
  · exact g32p_supplierForest_actual_025360
  · exact g32p_supplierForest_actual_025417
  · exact g32p_supplierForest_actual_025537
  · exact g32p_supplierForest_actual_025651
  · exact g32p_supplierForest_actual_025708
  · exact g32p_supplierForest_actual_025876
  · exact g32p_supplierForest_actual_025880
  · exact g32p_supplierForest_actual_025913
  · exact g32p_supplierForest_actual_026015
  · exact g32p_supplierForest_actual_026148
  · exact g32p_supplierForest_actual_026171
  · exact g32p_supplierForest_actual_026269
  · exact g32p_supplierForest_actual_026479
  · exact g32p_supplierForest_actual_026532
  · exact g32p_supplierForest_actual_026535
  · exact g32p_supplierForest_actual_026554
  · exact g32p_supplierForest_actual_026570
  · exact g32p_supplierForest_actual_026636
  · exact g32p_supplierForest_actual_026650
  · exact g32p_supplierForest_actual_026694
  · exact g32p_supplierForest_actual_026709
  · exact g32p_supplierForest_actual_026727
  · exact g32p_supplierForest_actual_026770
  · exact g32p_supplierForest_actual_026781
  · exact g32p_supplierForest_actual_026792
  · exact g32p_supplierForest_actual_026819
  · exact g32p_supplierForest_actual_026840
  · exact g32p_supplierForest_actual_026860
  · exact g32p_supplierForest_actual_026896
  · exact g32p_supplierForest_actual_026938
  · exact g32p_supplierForest_actual_026957
  · exact g32p_supplierForest_actual_026964
  · exact g32p_supplierForest_actual_027001
  · exact g32p_supplierForest_actual_027059
  · exact g32p_supplierForest_actual_027179
  · exact g32p_supplierForest_actual_027201
  · exact g32p_supplierForest_actual_027238
  · exact g32p_supplierForest_actual_027272
  · exact g32p_supplierForest_actual_027298
  · exact g32p_supplierForest_actual_027301
  · exact g32p_supplierForest_actual_027317
  · exact g32p_supplierForest_actual_027349
  · exact g32p_supplierForest_actual_027381
  · exact g32p_supplierForest_actual_027396
  · exact g32p_supplierForest_actual_027470
  · exact g32p_supplierForest_actual_027510
  · exact g32p_supplierForest_actual_027530
  · exact g32p_supplierForest_actual_027538
  · exact g32p_supplierForest_actual_027562
  · exact g32p_supplierForest_actual_027677
  · exact g32p_supplierForest_actual_027746
  · exact g32p_supplierForest_actual_027772
  · exact g32p_supplierForest_actual_027872
  · exact g32p_supplierForest_actual_027879
  · exact g32p_supplierForest_actual_027898
  · exact g32p_supplierForest_actual_027913
  · exact g32p_supplierForest_actual_027977
  · exact g32p_supplierForest_actual_028017
  · exact g32p_supplierForest_actual_028057
  · exact g32p_supplierForest_actual_028165
  · exact g32p_supplierForest_actual_028198
  · exact g32p_supplierForest_actual_028577
  · exact g32p_supplierForest_actual_028588
  · exact g32p_supplierForest_actual_028868
  · exact g32p_supplierForest_actual_028871
  · exact g32p_supplierForest_actual_029089
  · exact g32p_supplierForest_actual_029108
  · exact g32p_supplierForest_actual_029136
  · exact g32p_supplierForest_actual_029149
  · exact g32p_supplierForest_actual_029379
  · exact g32p_supplierForest_actual_029412
  · exact g32p_supplierForest_actual_029443
  · exact g32p_supplierForest_actual_029490
  · exact g32p_supplierForest_actual_029584
  · exact g32p_supplierForest_actual_029628
  · exact g32p_supplierForest_actual_029645
  · exact g32p_supplierForest_actual_029664
  · exact g32p_supplierForest_actual_029696
  · exact g32p_supplierForest_actual_029731
  · exact g32p_supplierForest_actual_029838
  · exact g32p_supplierForest_actual_029911
  · exact g32p_supplierForest_actual_029915
  · exact g32p_supplierForest_actual_029943
  · exact g32p_supplierForest_actual_030011
  · exact g32p_supplierForest_actual_030039
  · exact g32p_supplierForest_actual_030041
  · exact g32p_supplierForest_actual_030124
  · exact g32p_supplierForest_actual_030210
  · exact g32p_supplierForest_actual_030358
  · exact g32p_supplierForest_actual_030389
  · exact g32p_supplierForest_actual_030441
  · exact g32p_supplierForest_actual_030452
  · exact g32p_supplierForest_actual_030535
  · exact g32p_supplierForest_actual_030591
  · exact g32p_supplierForest_actual_030695
  · exact g32p_supplierForest_actual_030717
  · exact g32p_supplierForest_actual_030886
  · exact g32p_supplierForest_actual_030910
  · exact g32p_supplierForest_actual_030912
  · exact g32p_supplierForest_actual_030976
  · exact g32p_supplierForest_actual_031167
  · exact g32p_supplierForest_actual_031243
  · exact g32p_supplierForest_actual_031298
  · exact g32p_supplierForest_actual_031310
  · exact g32p_supplierForest_actual_031428
  · exact g32p_supplierForest_actual_031562
  · exact g32p_supplierForest_actual_031618
  · exact g32p_supplierForest_actual_031676
  · exact g32p_supplierForest_actual_031700
  · exact g32p_supplierForest_actual_031719
  · exact g32p_supplierForest_actual_031721
  · exact g32p_supplierForest_actual_031932
  · exact g32p_supplierForest_actual_031959
  · exact g32p_supplierForest_actual_031983
  · exact g32p_supplierForest_actual_032065
  · exact g32p_supplierForest_actual_032089
  · exact g32p_supplierForest_actual_032226
  · exact g32p_supplierForest_actual_032240
  · exact g32p_supplierForest_actual_032242
  · exact g32p_supplierForest_actual_032273
  · exact g32p_supplierForest_actual_032351
  · exact g32p_supplierForest_actual_032405
  · exact g32p_supplierForest_actual_032453
  · exact g32p_supplierForest_actual_032538
  · exact g32p_supplierForest_actual_032667
  · exact g32p_supplierForest_actual_032708
  · exact g32p_supplierForest_actual_032824
  · exact g32p_supplierForest_actual_032918
  · exact g32p_supplierForest_actual_032929
  · exact g32p_supplierForest_actual_033014
  · exact g32p_supplierForest_actual_033132
  · exact g32p_supplierForest_actual_033147
  · exact g32p_supplierForest_actual_033194
  · exact g32p_supplierForest_actual_033198
  · exact g32p_supplierForest_actual_033205
  · exact g32p_supplierForest_actual_033265
  · exact g32p_supplierForest_actual_033280
  · exact g32p_supplierForest_actual_033354
  · exact g32p_supplierForest_actual_033459
  · exact g32p_supplierForest_actual_033537
  · exact g32p_supplierForest_actual_033584
  · exact g32p_supplierForest_actual_033608
  · exact g32p_supplierForest_actual_033965
  · exact g32p_supplierForest_actual_034004
  · exact g32p_supplierForest_actual_034019
  · exact g32p_supplierForest_actual_034173
  · exact g32p_supplierForest_actual_034225
  · exact g32p_supplierForest_actual_034234
  · exact g32p_supplierForest_actual_034448
  · exact g32p_supplierForest_actual_034481
  · exact g32p_supplierForest_actual_034629
  · exact g32p_supplierForest_actual_034756
  · exact g32p_supplierForest_actual_034945
  · exact g32p_supplierForest_actual_034955
  · exact g32p_supplierForest_actual_035068
  · exact g32p_supplierForest_actual_035071
  · exact g32p_supplierForest_actual_035165
  · exact g32p_supplierForest_actual_035219
  · exact g32p_supplierForest_actual_035275
  · exact g32p_supplierForest_actual_035421
  · exact g32p_supplierForest_actual_035444
  · exact g32p_supplierForest_actual_035480
  · exact g32p_supplierForest_actual_035533
  · exact g32p_supplierForest_actual_035543
  · exact g32p_supplierForest_actual_035544
  · exact g32p_supplierForest_actual_035555
  · exact g32p_supplierForest_actual_035576
  · exact g32p_supplierForest_actual_035685
  · exact g32p_supplierForest_actual_035707
  · exact g32p_supplierForest_actual_036016
  · exact g32p_supplierForest_actual_036022
  · exact g32p_supplierForest_actual_036030
  · exact g32p_supplierForest_actual_036059
  · exact g32p_supplierForest_actual_036071
  · exact g32p_supplierForest_actual_036105
  · exact g32p_supplierForest_actual_036164
  · exact g32p_supplierForest_actual_036167
  · exact g32p_supplierForest_actual_036191
  · exact g32p_supplierForest_actual_036223
  · exact g32p_supplierForest_actual_036264
  · exact g32p_supplierForest_actual_036268
  · exact g32p_supplierForest_actual_036317
  · exact g32p_supplierForest_actual_036318
  · exact g32p_supplierForest_actual_036341
  · exact g32p_supplierForest_actual_036485
  · exact g32p_supplierForest_actual_036537
  · exact g32p_supplierForest_actual_036607
  · exact g32p_supplierForest_actual_036685
  · exact g32p_supplierForest_actual_036705
  · exact g32p_supplierForest_actual_036731
  · exact g32p_supplierForest_actual_036748
  · exact g32p_supplierForest_actual_036768
  · exact g32p_supplierForest_actual_036807
  · exact g32p_supplierForest_actual_036890
  · exact g32p_supplierForest_actual_036944
  · exact g32p_supplierForest_actual_036967
  · exact g32p_supplierForest_actual_037054
  · exact g32p_supplierForest_actual_037055
  · exact g32p_supplierForest_actual_037125
  · exact g32p_supplierForest_actual_037135
  · exact g32p_supplierForest_actual_037149
  · exact g32p_supplierForest_actual_037202
  · exact g32p_supplierForest_actual_037275
  · exact g32p_supplierForest_actual_037397
  · exact g32p_supplierForest_actual_037457
  · exact g32p_supplierForest_actual_037475
  · exact g32p_supplierForest_actual_037482
  · exact g32p_supplierForest_actual_037541
  · exact g32p_supplierForest_actual_037556
  · exact g32p_supplierForest_actual_037594
  · exact g32p_supplierForest_actual_037616
  · exact g32p_supplierForest_actual_037632
  · exact g32p_supplierForest_actual_037635

def g32p_supplierForest_nodes_134 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_037687 else g32p_supplierForest_node_037711) else (if i.val < 3 then g32p_supplierForest_node_037741 else g32p_supplierForest_node_037746)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_037810 else g32p_supplierForest_node_037895) else (if i.val < 7 then g32p_supplierForest_node_037906 else g32p_supplierForest_node_037936))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_037997 else g32p_supplierForest_node_038017) else (if i.val < 11 then g32p_supplierForest_node_038025 else g32p_supplierForest_node_038033)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_038047 else g32p_supplierForest_node_038078) else (if i.val < 15 then g32p_supplierForest_node_038126 else g32p_supplierForest_node_038220)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_038246 else g32p_supplierForest_node_038272) else (if i.val < 19 then g32p_supplierForest_node_038275 else g32p_supplierForest_node_038356)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_038365 else g32p_supplierForest_node_038404) else (if i.val < 23 then g32p_supplierForest_node_038473 else g32p_supplierForest_node_038579))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_038705 else g32p_supplierForest_node_038794) else (if i.val < 27 then g32p_supplierForest_node_038822 else g32p_supplierForest_node_038865)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_038871 else g32p_supplierForest_node_038875) else (if i.val < 31 then g32p_supplierForest_node_038984 else g32p_supplierForest_node_039026))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_039046 else g32p_supplierForest_node_039066) else (if i.val < 35 then g32p_supplierForest_node_039093 else g32p_supplierForest_node_039112)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_039173 else g32p_supplierForest_node_039191) else (if i.val < 39 then g32p_supplierForest_node_039201 else g32p_supplierForest_node_039351))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_039355 else g32p_supplierForest_node_039365) else (if i.val < 43 then g32p_supplierForest_node_039424 else g32p_supplierForest_node_039587)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_039615 else g32p_supplierForest_node_039668) else (if i.val < 47 then g32p_supplierForest_node_039675 else g32p_supplierForest_node_039692)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_039702 else g32p_supplierForest_node_039766) else (if i.val < 51 then g32p_supplierForest_node_039825 else g32p_supplierForest_node_039838)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_039970 else g32p_supplierForest_node_039983) else (if i.val < 55 then g32p_supplierForest_node_040217 else g32p_supplierForest_node_040275))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_040288 else g32p_supplierForest_node_040320) else (if i.val < 59 then g32p_supplierForest_node_040329 else g32p_supplierForest_node_040397)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_040536 else g32p_supplierForest_node_040571) else (if i.val < 63 then g32p_supplierForest_node_040671 else g32p_supplierForest_node_040682)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_040684 else g32p_supplierForest_node_040902) else (if i.val < 67 then g32p_supplierForest_node_040906 else g32p_supplierForest_node_040986)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_041021 else g32p_supplierForest_node_041049) else (if i.val < 71 then g32p_supplierForest_node_041088 else g32p_supplierForest_node_041166))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_041194 else g32p_supplierForest_node_041229) else (if i.val < 75 then g32p_supplierForest_node_041334 else g32p_supplierForest_node_041522)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_041653 else g32p_supplierForest_node_041689) else (if i.val < 79 then g32p_supplierForest_node_041725 else g32p_supplierForest_node_041734)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_041738 else g32p_supplierForest_node_041775) else (if i.val < 83 then g32p_supplierForest_node_041846 else g32p_supplierForest_node_041852)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_041876 else g32p_supplierForest_node_041924) else (if i.val < 87 then g32p_supplierForest_node_041950 else g32p_supplierForest_node_042088))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_042123 else g32p_supplierForest_node_042127) else (if i.val < 91 then g32p_supplierForest_node_042137 else g32p_supplierForest_node_042141)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_042160 else g32p_supplierForest_node_042173) else (if i.val < 95 then g32p_supplierForest_node_042273 else g32p_supplierForest_node_042294))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_042298 else g32p_supplierForest_node_042303) else (if i.val < 99 then g32p_supplierForest_node_042315 else g32p_supplierForest_node_042340)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_042388 else g32p_supplierForest_node_042392) else (if i.val < 103 then g32p_supplierForest_node_042472 else g32p_supplierForest_node_042515))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_042537 else g32p_supplierForest_node_042601) else (if i.val < 107 then g32p_supplierForest_node_042806 else g32p_supplierForest_node_042812)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_042833 else g32p_supplierForest_node_042865) else (if i.val < 111 then g32p_supplierForest_node_042880 else g32p_supplierForest_node_042884)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_042948 else g32p_supplierForest_node_042991) else (if i.val < 115 then g32p_supplierForest_node_043065 else g32p_supplierForest_node_043116)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_043207 else g32p_supplierForest_node_043252) else (if i.val < 119 then g32p_supplierForest_node_043279 else g32p_supplierForest_node_043414))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_043527 else g32p_supplierForest_node_043670) else (if i.val < 123 then g32p_supplierForest_node_043684 else g32p_supplierForest_node_043816)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_043876 else g32p_supplierForest_node_043885) else (if i.val < 127 then g32p_supplierForest_node_043913 else g32p_supplierForest_node_043946))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_043978 else g32p_supplierForest_node_044030) else (if i.val < 131 then g32p_supplierForest_node_044048 else g32p_supplierForest_node_044281)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_044283 else g32p_supplierForest_node_044295) else (if i.val < 135 then g32p_supplierForest_node_044335 else g32p_supplierForest_node_044384))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_044472 else g32p_supplierForest_node_044520) else (if i.val < 139 then g32p_supplierForest_node_044612 else g32p_supplierForest_node_044757)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_044831 else g32p_supplierForest_node_044836) else (if i.val < 143 then g32p_supplierForest_node_045032 else g32p_supplierForest_node_045037)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_045122 else g32p_supplierForest_node_045132) else (if i.val < 147 then g32p_supplierForest_node_045137 else g32p_supplierForest_node_045184)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_045223 else g32p_supplierForest_node_045292) else (if i.val < 151 then g32p_supplierForest_node_045382 else g32p_supplierForest_node_045405))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_045522 else g32p_supplierForest_node_045608) else (if i.val < 155 then g32p_supplierForest_node_045649 else g32p_supplierForest_node_045674)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_045879 else g32p_supplierForest_node_046034) else (if i.val < 159 then g32p_supplierForest_node_046320 else g32p_supplierForest_node_046324))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_046405 else g32p_supplierForest_node_046420) else (if i.val < 163 then g32p_supplierForest_node_046435 else g32p_supplierForest_node_046515)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_046537 else g32p_supplierForest_node_046615) else (if i.val < 167 then g32p_supplierForest_node_046643 else g32p_supplierForest_node_046931))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_046946 else g32p_supplierForest_node_047050) else (if i.val < 171 then g32p_supplierForest_node_047146 else g32p_supplierForest_node_047154)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_047192 else g32p_supplierForest_node_047234) else (if i.val < 175 then g32p_supplierForest_node_047289 else g32p_supplierForest_node_047316)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_047318 else g32p_supplierForest_node_047336) else (if i.val < 179 then g32p_supplierForest_node_047340 else g32p_supplierForest_node_047377)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_047393 else g32p_supplierForest_node_047557) else (if i.val < 183 then g32p_supplierForest_node_047603 else g32p_supplierForest_node_047717))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_047836 else g32p_supplierForest_node_047840) else (if i.val < 187 then g32p_supplierForest_node_047880 else g32p_supplierForest_node_047888)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_047906 else g32p_supplierForest_node_048037) else (if i.val < 191 then g32p_supplierForest_node_048048 else g32p_supplierForest_node_048092)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_048113 else g32p_supplierForest_node_048153) else (if i.val < 195 then g32p_supplierForest_node_048191 else g32p_supplierForest_node_048259)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_048299 else g32p_supplierForest_node_048363) else (if i.val < 199 then g32p_supplierForest_node_048379 else g32p_supplierForest_node_048440))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_048452 else g32p_supplierForest_node_048481) else (if i.val < 203 then g32p_supplierForest_node_048483 else g32p_supplierForest_node_048574)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_048582 else g32p_supplierForest_node_048589) else (if i.val < 207 then g32p_supplierForest_node_048633 else g32p_supplierForest_node_048642)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_048856 else g32p_supplierForest_node_048896) else (if i.val < 211 then g32p_supplierForest_node_048900 else g32p_supplierForest_node_048955)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_049043 else g32p_supplierForest_node_049069) else (if i.val < 215 then g32p_supplierForest_node_049104 else g32p_supplierForest_node_049154))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_049158 else g32p_supplierForest_node_049200) else (if i.val < 219 then g32p_supplierForest_node_049204 else g32p_supplierForest_node_049290)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_049302 else g32p_supplierForest_node_049354) else (if i.val < 223 then g32p_supplierForest_node_049423 else g32p_supplierForest_node_049430))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_049432 else g32p_supplierForest_node_049482) else (if i.val < 227 then g32p_supplierForest_node_049519 else g32p_supplierForest_node_049541)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_049698 else g32p_supplierForest_node_049700) else (if i.val < 231 then g32p_supplierForest_node_049767 else g32p_supplierForest_node_049805))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_049829 else g32p_supplierForest_node_049889) else (if i.val < 235 then g32p_supplierForest_node_049908 else g32p_supplierForest_node_049936)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_049939 else g32p_supplierForest_node_049959) else (if i.val < 239 then g32p_supplierForest_node_050015 else g32p_supplierForest_node_050062)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_050071 else g32p_supplierForest_node_050076) else (if i.val < 243 then g32p_supplierForest_node_050103 else g32p_supplierForest_node_050104)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_050206 else g32p_supplierForest_node_050218) else (if i.val < 247 then g32p_supplierForest_node_050250 else g32p_supplierForest_node_050260))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_050367 else g32p_supplierForest_node_050370) else (if i.val < 251 then g32p_supplierForest_node_050379 else g32p_supplierForest_node_050409)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_050433 else g32p_supplierForest_node_050539) else (if i.val < 255 then g32p_supplierForest_node_050543 else g32p_supplierForest_node_050558))))))))

def g32p_supplierForest_classes_134 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 62 else 57) else (if i.val < 3 then 29 else 30)) else (if i.val < 6 then (if i.val < 5 then 17 else 29) else (if i.val < 7 then 57 else 16))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 57) else (if i.val < 11 then 57 else 63)) else (if i.val < 14 then (if i.val < 13 then 57 else 16) else (if i.val < 15 then 59 else 16)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 33 else 30) else (if i.val < 19 then 30 else 30)) else (if i.val < 22 then (if i.val < 21 then 30 else 30) else (if i.val < 23 then 30 else 57))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 29 else 16) else (if i.val < 27 then 30 else 57)) else (if i.val < 30 then (if i.val < 29 then 16 else 57) else (if i.val < 31 then 57 else 30))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 57 else 29) else (if i.val < 35 then 30 else 57)) else (if i.val < 38 then (if i.val < 37 then 30 else 57) else (if i.val < 39 then 57 else 57))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 57 else 30) else (if i.val < 43 then 30 else 36)) else (if i.val < 46 then (if i.val < 45 then 57 else 60) else (if i.val < 47 then 63 else 57)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 15 else 57) else (if i.val < 51 then 16 else 17)) else (if i.val < 54 then (if i.val < 53 then 16 else 57) else (if i.val < 55 then 57 else 63))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 30 else 57) else (if i.val < 59 then 16 else 60)) else (if i.val < 62 then (if i.val < 61 then 57 else 16) else (if i.val < 63 then 30 else 57)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 57 else 57) else (if i.val < 67 then 57 else 60)) else (if i.val < 70 then (if i.val < 69 then 16 else 57) else (if i.val < 71 then 14 else 57))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 57 else 36) else (if i.val < 75 then 16 else 57)) else (if i.val < 78 then (if i.val < 77 then 57 else 16) else (if i.val < 79 then 57 else 62)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 57 else 14) else (if i.val < 83 then 57 else 57)) else (if i.val < 86 then (if i.val < 85 then 30 else 57) else (if i.val < 87 then 16 else 30))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 57) else (if i.val < 91 then 14 else 15)) else (if i.val < 94 then (if i.val < 93 then 57 else 57) else (if i.val < 95 then 57 else 57))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 16 else 57) else (if i.val < 99 then 30 else 57)) else (if i.val < 102 then (if i.val < 101 then 30 else 30) else (if i.val < 103 then 30 else 16))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 15 else 57) else (if i.val < 107 then 60 else 57)) else (if i.val < 110 then (if i.val < 109 then 58 else 30) else (if i.val < 111 then 15 else 30)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 57 else 33) else (if i.val < 115 then 60 else 57)) else (if i.val < 118 then (if i.val < 117 then 57 else 57) else (if i.val < 119 then 30 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 57 else 36) else (if i.val < 123 then 57 else 30)) else (if i.val < 126 then (if i.val < 125 then 57 else 59) else (if i.val < 127 then 30 else 30))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 57 else 30) else (if i.val < 131 then 57 else 62)) else (if i.val < 134 then (if i.val < 133 then 57 else 14) else (if i.val < 135 then 60 else 30))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 38 else 21) else (if i.val < 139 then 21 else 38)) else (if i.val < 142 then (if i.val < 141 then 39 else 22) else (if i.val < 143 then 38 else 21)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 38 else 38) else (if i.val < 147 then 38 else 22)) else (if i.val < 150 then (if i.val < 149 then 22 else 7) else (if i.val < 151 then 7 else 21))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 21 else 38) else (if i.val < 155 then 38 else 70)) else (if i.val < 158 then (if i.val < 157 then 21 else 38) else (if i.val < 159 then 74 else 38))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 74 else 74) else (if i.val < 163 then 41 else 38)) else (if i.val < 166 then (if i.val < 165 then 38 else 38) else (if i.val < 167 then 22 else 40))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 38) else (if i.val < 171 then 38 else 41)) else (if i.val < 174 then (if i.val < 173 then 41 else 38) else (if i.val < 175 then 38 else 40)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 38 else 21) else (if i.val < 179 then 41 else 38)) else (if i.val < 182 then (if i.val < 181 then 38 else 21) else (if i.val < 183 then 21 else 22))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 38 else 22) else (if i.val < 187 then 21 else 43)) else (if i.val < 190 then (if i.val < 189 then 20 else 38) else (if i.val < 191 then 38 else 41)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 22 else 21) else (if i.val < 195 then 38 else 21)) else (if i.val < 198 then (if i.val < 197 then 38 else 38) else (if i.val < 199 then 74 else 70))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 70 else 73) else (if i.val < 203 then 74 else 22)) else (if i.val < 206 then (if i.val < 205 then 38 else 71) else (if i.val < 207 then 22 else 38)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 21 else 21) else (if i.val < 211 then 38 else 22)) else (if i.val < 214 then (if i.val < 213 then 38 else 38) else (if i.val < 215 then 22 else 38))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 38 else 38) else (if i.val < 219 then 38 else 38)) else (if i.val < 222 then (if i.val < 221 then 38 else 68) else (if i.val < 223 then 38 else 42))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 21 else 22) else (if i.val < 227 then 38 else 42)) else (if i.val < 230 then (if i.val < 229 then 21 else 22) else (if i.val < 231 then 38 else 71))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 21 else 21) else (if i.val < 235 then 38 else 22)) else (if i.val < 238 then (if i.val < 237 then 22 else 22) else (if i.val < 239 then 38 else 22)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 21 else 21) else (if i.val < 243 then 68 else 22)) else (if i.val < 246 then (if i.val < 245 then 43 else 38) else (if i.val < 247 then 38 else 22))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 39 else 39) else (if i.val < 251 then 38 else 39)) else (if i.val < 254 then (if i.val < 253 then 38 else 38) else (if i.val < 255 then 70 else 38))))))))

theorem g32p_supplierForest_actual_134 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_134 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_134 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_037687
  · exact g32p_supplierForest_actual_037711
  · exact g32p_supplierForest_actual_037741
  · exact g32p_supplierForest_actual_037746
  · exact g32p_supplierForest_actual_037810
  · exact g32p_supplierForest_actual_037895
  · exact g32p_supplierForest_actual_037906
  · exact g32p_supplierForest_actual_037936
  · exact g32p_supplierForest_actual_037997
  · exact g32p_supplierForest_actual_038017
  · exact g32p_supplierForest_actual_038025
  · exact g32p_supplierForest_actual_038033
  · exact g32p_supplierForest_actual_038047
  · exact g32p_supplierForest_actual_038078
  · exact g32p_supplierForest_actual_038126
  · exact g32p_supplierForest_actual_038220
  · exact g32p_supplierForest_actual_038246
  · exact g32p_supplierForest_actual_038272
  · exact g32p_supplierForest_actual_038275
  · exact g32p_supplierForest_actual_038356
  · exact g32p_supplierForest_actual_038365
  · exact g32p_supplierForest_actual_038404
  · exact g32p_supplierForest_actual_038473
  · exact g32p_supplierForest_actual_038579
  · exact g32p_supplierForest_actual_038705
  · exact g32p_supplierForest_actual_038794
  · exact g32p_supplierForest_actual_038822
  · exact g32p_supplierForest_actual_038865
  · exact g32p_supplierForest_actual_038871
  · exact g32p_supplierForest_actual_038875
  · exact g32p_supplierForest_actual_038984
  · exact g32p_supplierForest_actual_039026
  · exact g32p_supplierForest_actual_039046
  · exact g32p_supplierForest_actual_039066
  · exact g32p_supplierForest_actual_039093
  · exact g32p_supplierForest_actual_039112
  · exact g32p_supplierForest_actual_039173
  · exact g32p_supplierForest_actual_039191
  · exact g32p_supplierForest_actual_039201
  · exact g32p_supplierForest_actual_039351
  · exact g32p_supplierForest_actual_039355
  · exact g32p_supplierForest_actual_039365
  · exact g32p_supplierForest_actual_039424
  · exact g32p_supplierForest_actual_039587
  · exact g32p_supplierForest_actual_039615
  · exact g32p_supplierForest_actual_039668
  · exact g32p_supplierForest_actual_039675
  · exact g32p_supplierForest_actual_039692
  · exact g32p_supplierForest_actual_039702
  · exact g32p_supplierForest_actual_039766
  · exact g32p_supplierForest_actual_039825
  · exact g32p_supplierForest_actual_039838
  · exact g32p_supplierForest_actual_039970
  · exact g32p_supplierForest_actual_039983
  · exact g32p_supplierForest_actual_040217
  · exact g32p_supplierForest_actual_040275
  · exact g32p_supplierForest_actual_040288
  · exact g32p_supplierForest_actual_040320
  · exact g32p_supplierForest_actual_040329
  · exact g32p_supplierForest_actual_040397
  · exact g32p_supplierForest_actual_040536
  · exact g32p_supplierForest_actual_040571
  · exact g32p_supplierForest_actual_040671
  · exact g32p_supplierForest_actual_040682
  · exact g32p_supplierForest_actual_040684
  · exact g32p_supplierForest_actual_040902
  · exact g32p_supplierForest_actual_040906
  · exact g32p_supplierForest_actual_040986
  · exact g32p_supplierForest_actual_041021
  · exact g32p_supplierForest_actual_041049
  · exact g32p_supplierForest_actual_041088
  · exact g32p_supplierForest_actual_041166
  · exact g32p_supplierForest_actual_041194
  · exact g32p_supplierForest_actual_041229
  · exact g32p_supplierForest_actual_041334
  · exact g32p_supplierForest_actual_041522
  · exact g32p_supplierForest_actual_041653
  · exact g32p_supplierForest_actual_041689
  · exact g32p_supplierForest_actual_041725
  · exact g32p_supplierForest_actual_041734
  · exact g32p_supplierForest_actual_041738
  · exact g32p_supplierForest_actual_041775
  · exact g32p_supplierForest_actual_041846
  · exact g32p_supplierForest_actual_041852
  · exact g32p_supplierForest_actual_041876
  · exact g32p_supplierForest_actual_041924
  · exact g32p_supplierForest_actual_041950
  · exact g32p_supplierForest_actual_042088
  · exact g32p_supplierForest_actual_042123
  · exact g32p_supplierForest_actual_042127
  · exact g32p_supplierForest_actual_042137
  · exact g32p_supplierForest_actual_042141
  · exact g32p_supplierForest_actual_042160
  · exact g32p_supplierForest_actual_042173
  · exact g32p_supplierForest_actual_042273
  · exact g32p_supplierForest_actual_042294
  · exact g32p_supplierForest_actual_042298
  · exact g32p_supplierForest_actual_042303
  · exact g32p_supplierForest_actual_042315
  · exact g32p_supplierForest_actual_042340
  · exact g32p_supplierForest_actual_042388
  · exact g32p_supplierForest_actual_042392
  · exact g32p_supplierForest_actual_042472
  · exact g32p_supplierForest_actual_042515
  · exact g32p_supplierForest_actual_042537
  · exact g32p_supplierForest_actual_042601
  · exact g32p_supplierForest_actual_042806
  · exact g32p_supplierForest_actual_042812
  · exact g32p_supplierForest_actual_042833
  · exact g32p_supplierForest_actual_042865
  · exact g32p_supplierForest_actual_042880
  · exact g32p_supplierForest_actual_042884
  · exact g32p_supplierForest_actual_042948
  · exact g32p_supplierForest_actual_042991
  · exact g32p_supplierForest_actual_043065
  · exact g32p_supplierForest_actual_043116
  · exact g32p_supplierForest_actual_043207
  · exact g32p_supplierForest_actual_043252
  · exact g32p_supplierForest_actual_043279
  · exact g32p_supplierForest_actual_043414
  · exact g32p_supplierForest_actual_043527
  · exact g32p_supplierForest_actual_043670
  · exact g32p_supplierForest_actual_043684
  · exact g32p_supplierForest_actual_043816
  · exact g32p_supplierForest_actual_043876
  · exact g32p_supplierForest_actual_043885
  · exact g32p_supplierForest_actual_043913
  · exact g32p_supplierForest_actual_043946
  · exact g32p_supplierForest_actual_043978
  · exact g32p_supplierForest_actual_044030
  · exact g32p_supplierForest_actual_044048
  · exact g32p_supplierForest_actual_044281
  · exact g32p_supplierForest_actual_044283
  · exact g32p_supplierForest_actual_044295
  · exact g32p_supplierForest_actual_044335
  · exact g32p_supplierForest_actual_044384
  · exact g32p_supplierForest_actual_044472
  · exact g32p_supplierForest_actual_044520
  · exact g32p_supplierForest_actual_044612
  · exact g32p_supplierForest_actual_044757
  · exact g32p_supplierForest_actual_044831
  · exact g32p_supplierForest_actual_044836
  · exact g32p_supplierForest_actual_045032
  · exact g32p_supplierForest_actual_045037
  · exact g32p_supplierForest_actual_045122
  · exact g32p_supplierForest_actual_045132
  · exact g32p_supplierForest_actual_045137
  · exact g32p_supplierForest_actual_045184
  · exact g32p_supplierForest_actual_045223
  · exact g32p_supplierForest_actual_045292
  · exact g32p_supplierForest_actual_045382
  · exact g32p_supplierForest_actual_045405
  · exact g32p_supplierForest_actual_045522
  · exact g32p_supplierForest_actual_045608
  · exact g32p_supplierForest_actual_045649
  · exact g32p_supplierForest_actual_045674
  · exact g32p_supplierForest_actual_045879
  · exact g32p_supplierForest_actual_046034
  · exact g32p_supplierForest_actual_046320
  · exact g32p_supplierForest_actual_046324
  · exact g32p_supplierForest_actual_046405
  · exact g32p_supplierForest_actual_046420
  · exact g32p_supplierForest_actual_046435
  · exact g32p_supplierForest_actual_046515
  · exact g32p_supplierForest_actual_046537
  · exact g32p_supplierForest_actual_046615
  · exact g32p_supplierForest_actual_046643
  · exact g32p_supplierForest_actual_046931
  · exact g32p_supplierForest_actual_046946
  · exact g32p_supplierForest_actual_047050
  · exact g32p_supplierForest_actual_047146
  · exact g32p_supplierForest_actual_047154
  · exact g32p_supplierForest_actual_047192
  · exact g32p_supplierForest_actual_047234
  · exact g32p_supplierForest_actual_047289
  · exact g32p_supplierForest_actual_047316
  · exact g32p_supplierForest_actual_047318
  · exact g32p_supplierForest_actual_047336
  · exact g32p_supplierForest_actual_047340
  · exact g32p_supplierForest_actual_047377
  · exact g32p_supplierForest_actual_047393
  · exact g32p_supplierForest_actual_047557
  · exact g32p_supplierForest_actual_047603
  · exact g32p_supplierForest_actual_047717
  · exact g32p_supplierForest_actual_047836
  · exact g32p_supplierForest_actual_047840
  · exact g32p_supplierForest_actual_047880
  · exact g32p_supplierForest_actual_047888
  · exact g32p_supplierForest_actual_047906
  · exact g32p_supplierForest_actual_048037
  · exact g32p_supplierForest_actual_048048
  · exact g32p_supplierForest_actual_048092
  · exact g32p_supplierForest_actual_048113
  · exact g32p_supplierForest_actual_048153
  · exact g32p_supplierForest_actual_048191
  · exact g32p_supplierForest_actual_048259
  · exact g32p_supplierForest_actual_048299
  · exact g32p_supplierForest_actual_048363
  · exact g32p_supplierForest_actual_048379
  · exact g32p_supplierForest_actual_048440
  · exact g32p_supplierForest_actual_048452
  · exact g32p_supplierForest_actual_048481
  · exact g32p_supplierForest_actual_048483
  · exact g32p_supplierForest_actual_048574
  · exact g32p_supplierForest_actual_048582
  · exact g32p_supplierForest_actual_048589
  · exact g32p_supplierForest_actual_048633
  · exact g32p_supplierForest_actual_048642
  · exact g32p_supplierForest_actual_048856
  · exact g32p_supplierForest_actual_048896
  · exact g32p_supplierForest_actual_048900
  · exact g32p_supplierForest_actual_048955
  · exact g32p_supplierForest_actual_049043
  · exact g32p_supplierForest_actual_049069
  · exact g32p_supplierForest_actual_049104
  · exact g32p_supplierForest_actual_049154
  · exact g32p_supplierForest_actual_049158
  · exact g32p_supplierForest_actual_049200
  · exact g32p_supplierForest_actual_049204
  · exact g32p_supplierForest_actual_049290
  · exact g32p_supplierForest_actual_049302
  · exact g32p_supplierForest_actual_049354
  · exact g32p_supplierForest_actual_049423
  · exact g32p_supplierForest_actual_049430
  · exact g32p_supplierForest_actual_049432
  · exact g32p_supplierForest_actual_049482
  · exact g32p_supplierForest_actual_049519
  · exact g32p_supplierForest_actual_049541
  · exact g32p_supplierForest_actual_049698
  · exact g32p_supplierForest_actual_049700
  · exact g32p_supplierForest_actual_049767
  · exact g32p_supplierForest_actual_049805
  · exact g32p_supplierForest_actual_049829
  · exact g32p_supplierForest_actual_049889
  · exact g32p_supplierForest_actual_049908
  · exact g32p_supplierForest_actual_049936
  · exact g32p_supplierForest_actual_049939
  · exact g32p_supplierForest_actual_049959
  · exact g32p_supplierForest_actual_050015
  · exact g32p_supplierForest_actual_050062
  · exact g32p_supplierForest_actual_050071
  · exact g32p_supplierForest_actual_050076
  · exact g32p_supplierForest_actual_050103
  · exact g32p_supplierForest_actual_050104
  · exact g32p_supplierForest_actual_050206
  · exact g32p_supplierForest_actual_050218
  · exact g32p_supplierForest_actual_050250
  · exact g32p_supplierForest_actual_050260
  · exact g32p_supplierForest_actual_050367
  · exact g32p_supplierForest_actual_050370
  · exact g32p_supplierForest_actual_050379
  · exact g32p_supplierForest_actual_050409
  · exact g32p_supplierForest_actual_050433
  · exact g32p_supplierForest_actual_050539
  · exact g32p_supplierForest_actual_050543
  · exact g32p_supplierForest_actual_050558

def g32p_supplierForest_nodes_135 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_050601 else g32p_supplierForest_node_050602) else (if i.val < 3 then g32p_supplierForest_node_050635 else g32p_supplierForest_node_050682)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_050710 else g32p_supplierForest_node_050726) else (if i.val < 7 then g32p_supplierForest_node_050765 else g32p_supplierForest_node_050817))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_050846 else g32p_supplierForest_node_050874) else (if i.val < 11 then g32p_supplierForest_node_050881 else g32p_supplierForest_node_051034)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_051191 else g32p_supplierForest_node_051196) else (if i.val < 15 then g32p_supplierForest_node_051267 else g32p_supplierForest_node_051294)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_051406 else g32p_supplierForest_node_051451) else (if i.val < 19 then g32p_supplierForest_node_051462 else g32p_supplierForest_node_051609)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_051628 else g32p_supplierForest_node_051645) else (if i.val < 23 then g32p_supplierForest_node_051696 else g32p_supplierForest_node_051761))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_051812 else g32p_supplierForest_node_051833) else (if i.val < 27 then g32p_supplierForest_node_051977 else g32p_supplierForest_node_051993)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_052096 else g32p_supplierForest_node_052108) else (if i.val < 31 then g32p_supplierForest_node_052112 else g32p_supplierForest_node_052117))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_052134 else g32p_supplierForest_node_052192) else (if i.val < 35 then g32p_supplierForest_node_052193 else g32p_supplierForest_node_052216)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_052285 else g32p_supplierForest_node_052290) else (if i.val < 39 then g32p_supplierForest_node_052360 else g32p_supplierForest_node_052461))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_052483 else g32p_supplierForest_node_052571) else (if i.val < 43 then g32p_supplierForest_node_052586 else g32p_supplierForest_node_052614)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_052646 else g32p_supplierForest_node_052686) else (if i.val < 47 then g32p_supplierForest_node_052692 else g32p_supplierForest_node_052767)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_052785 else g32p_supplierForest_node_052796) else (if i.val < 51 then g32p_supplierForest_node_052850 else g32p_supplierForest_node_052883)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_052938 else g32p_supplierForest_node_052942) else (if i.val < 55 then g32p_supplierForest_node_052953 else g32p_supplierForest_node_052963))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_053066 else g32p_supplierForest_node_053139) else (if i.val < 59 then g32p_supplierForest_node_053160 else g32p_supplierForest_node_053239)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_053257 else g32p_supplierForest_node_053332) else (if i.val < 63 then g32p_supplierForest_node_053355 else g32p_supplierForest_node_053378)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_053401 else g32p_supplierForest_node_053436) else (if i.val < 67 then g32p_supplierForest_node_053449 else g32p_supplierForest_node_053466)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_053502 else g32p_supplierForest_node_053504) else (if i.val < 71 then g32p_supplierForest_node_053543 else g32p_supplierForest_node_053630))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_053675 else g32p_supplierForest_node_053741) else (if i.val < 75 then g32p_supplierForest_node_053755 else g32p_supplierForest_node_053816)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_054021 else g32p_supplierForest_node_054175) else (if i.val < 79 then g32p_supplierForest_node_054267 else g32p_supplierForest_node_054339)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_054344 else g32p_supplierForest_node_054353) else (if i.val < 83 then g32p_supplierForest_node_054479 else g32p_supplierForest_node_054553)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_054561 else g32p_supplierForest_node_054599) else (if i.val < 87 then g32p_supplierForest_node_054668 else g32p_supplierForest_node_054680))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_054742 else g32p_supplierForest_node_054786) else (if i.val < 91 then g32p_supplierForest_node_054869 else g32p_supplierForest_node_054953)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_055038 else g32p_supplierForest_node_055043) else (if i.val < 95 then g32p_supplierForest_node_055092 else g32p_supplierForest_node_055419))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_055490 else g32p_supplierForest_node_055528) else (if i.val < 99 then g32p_supplierForest_node_055546 else g32p_supplierForest_node_055550)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_055637 else g32p_supplierForest_node_055665) else (if i.val < 103 then g32p_supplierForest_node_055677 else g32p_supplierForest_node_055696))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_055858 else g32p_supplierForest_node_055861) else (if i.val < 107 then g32p_supplierForest_node_055892 else g32p_supplierForest_node_055931)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_055933 else g32p_supplierForest_node_055958) else (if i.val < 111 then g32p_supplierForest_node_056056 else g32p_supplierForest_node_056057)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_056228 else g32p_supplierForest_node_056284) else (if i.val < 115 then g32p_supplierForest_node_056317 else g32p_supplierForest_node_056351)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_056396 else g32p_supplierForest_node_056397) else (if i.val < 119 then g32p_supplierForest_node_056440 else g32p_supplierForest_node_056467))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_056470 else g32p_supplierForest_node_056518) else (if i.val < 123 then g32p_supplierForest_node_056536 else g32p_supplierForest_node_056624)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_056695 else g32p_supplierForest_node_056778) else (if i.val < 127 then g32p_supplierForest_node_056895 else g32p_supplierForest_node_056950))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_057021 else g32p_supplierForest_node_057078) else (if i.val < 131 then g32p_supplierForest_node_057114 else g32p_supplierForest_node_057476)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_057486 else g32p_supplierForest_node_057524) else (if i.val < 135 then g32p_supplierForest_node_057540 else g32p_supplierForest_node_057589))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_057773 else g32p_supplierForest_node_058021) else (if i.val < 139 then g32p_supplierForest_node_058120 else g32p_supplierForest_node_058184)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_058220 else g32p_supplierForest_node_058283) else (if i.val < 143 then g32p_supplierForest_node_058372 else g32p_supplierForest_node_058432)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_058440 else g32p_supplierForest_node_058476) else (if i.val < 147 then g32p_supplierForest_node_058498 else g32p_supplierForest_node_058542)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_058572 else g32p_supplierForest_node_058591) else (if i.val < 151 then g32p_supplierForest_node_058600 else g32p_supplierForest_node_058613))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_058632 else g32p_supplierForest_node_058740) else (if i.val < 155 then g32p_supplierForest_node_058742 else g32p_supplierForest_node_058765)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_058776 else g32p_supplierForest_node_058862) else (if i.val < 159 then g32p_supplierForest_node_058875 else g32p_supplierForest_node_058906))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_058971 else g32p_supplierForest_node_059000) else (if i.val < 163 then g32p_supplierForest_node_059037 else g32p_supplierForest_node_059147)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_059153 else g32p_supplierForest_node_059165) else (if i.val < 167 then g32p_supplierForest_node_059267 else g32p_supplierForest_node_059432))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_059439 else g32p_supplierForest_node_059467) else (if i.val < 171 then g32p_supplierForest_node_059712 else g32p_supplierForest_node_059833)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_059853 else g32p_supplierForest_node_059895) else (if i.val < 175 then g32p_supplierForest_node_059929 else g32p_supplierForest_node_059937)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_059942 else g32p_supplierForest_node_059949) else (if i.val < 179 then g32p_supplierForest_node_059971 else g32p_supplierForest_node_059981)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_060002 else g32p_supplierForest_node_060020) else (if i.val < 183 then g32p_supplierForest_node_060107 else g32p_supplierForest_node_060138))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_060199 else g32p_supplierForest_node_060216) else (if i.val < 187 then g32p_supplierForest_node_060335 else g32p_supplierForest_node_060369)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_060524 else g32p_supplierForest_node_060607) else (if i.val < 191 then g32p_supplierForest_node_060649 else g32p_supplierForest_node_060807)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_060908 else g32p_supplierForest_node_060958) else (if i.val < 195 then g32p_supplierForest_node_060997 else g32p_supplierForest_node_061022)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_061045 else g32p_supplierForest_node_061058) else (if i.val < 199 then g32p_supplierForest_node_061174 else g32p_supplierForest_node_061220))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_061356 else g32p_supplierForest_node_061406) else (if i.val < 203 then g32p_supplierForest_node_061494 else g32p_supplierForest_node_061530)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_061561 else g32p_supplierForest_node_061567) else (if i.val < 207 then g32p_supplierForest_node_061591 else g32p_supplierForest_node_061649)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_061700 else g32p_supplierForest_node_061711) else (if i.val < 211 then g32p_supplierForest_node_061724 else g32p_supplierForest_node_061772)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_061816 else g32p_supplierForest_node_061817) else (if i.val < 215 then g32p_supplierForest_node_061850 else g32p_supplierForest_node_061872))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_061923 else g32p_supplierForest_node_062070) else (if i.val < 219 then g32p_supplierForest_node_062086 else g32p_supplierForest_node_062195)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_062323 else g32p_supplierForest_node_062544) else (if i.val < 223 then g32p_supplierForest_node_062555 else g32p_supplierForest_node_062567))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_062576 else g32p_supplierForest_node_062609) else (if i.val < 227 then g32p_supplierForest_node_062892 else g32p_supplierForest_node_062924)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_062937 else g32p_supplierForest_node_063003) else (if i.val < 231 then g32p_supplierForest_node_063026 else g32p_supplierForest_node_063095))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_063125 else g32p_supplierForest_node_063153) else (if i.val < 235 then g32p_supplierForest_node_063217 else g32p_supplierForest_node_063278)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_063281 else g32p_supplierForest_node_063371) else (if i.val < 239 then g32p_supplierForest_node_063398 else g32p_supplierForest_node_063399)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_063699 else g32p_supplierForest_node_063792) else (if i.val < 243 then g32p_supplierForest_node_063857 else g32p_supplierForest_node_063878)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_063938 else g32p_supplierForest_node_063978) else (if i.val < 247 then g32p_supplierForest_node_064020 else g32p_supplierForest_node_064036))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_064103 else g32p_supplierForest_node_064157) else (if i.val < 251 then g32p_supplierForest_node_064284 else g32p_supplierForest_node_064357)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_064405 else g32p_supplierForest_node_064408) else (if i.val < 255 then g32p_supplierForest_node_064421 else g32p_supplierForest_node_064440))))))))

def g32p_supplierForest_classes_135 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 38 else 38) else (if i.val < 3 then 73 else 38)) else (if i.val < 6 then (if i.val < 5 then 38 else 22) else (if i.val < 7 then 38 else 21))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 38 else 21) else (if i.val < 11 then 38 else 43)) else (if i.val < 14 then (if i.val < 13 then 21 else 21) else (if i.val < 15 then 38 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 21 else 38) else (if i.val < 19 then 21 else 38)) else (if i.val < 22 then (if i.val < 21 then 38 else 39) else (if i.val < 23 then 39 else 20))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 41 else 38) else (if i.val < 27 then 20 else 38)) else (if i.val < 30 then (if i.val < 29 then 38 else 38) else (if i.val < 31 then 22 else 21))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 21 else 73) else (if i.val < 35 then 22 else 21)) else (if i.val < 38 then (if i.val < 37 then 38 else 21) else (if i.val < 39 then 38 else 21))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 21 else 73) else (if i.val < 43 then 22 else 70)) else (if i.val < 46 then (if i.val < 45 then 21 else 21) else (if i.val < 47 then 22 else 22)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 38 else 21) else (if i.val < 51 then 22 else 22)) else (if i.val < 54 then (if i.val < 53 then 21 else 38) else (if i.val < 55 then 70 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 73) else (if i.val < 59 then 22 else 21)) else (if i.val < 62 then (if i.val < 61 then 71 else 68) else (if i.val < 63 then 38 else 38)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 21 else 21) else (if i.val < 67 then 41 else 38)) else (if i.val < 70 then (if i.val < 69 then 38 else 20) else (if i.val < 71 then 40 else 22))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 22 else 22) else (if i.val < 75 then 21 else 38)) else (if i.val < 78 then (if i.val < 77 then 21 else 21) else (if i.val < 79 then 38 else 38)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 38) else (if i.val < 83 then 41 else 21)) else (if i.val < 86 then (if i.val < 85 then 38 else 38) else (if i.val < 87 then 41 else 22))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 22 else 20) else (if i.val < 91 then 40 else 38)) else (if i.val < 94 then (if i.val < 93 then 22 else 38) else (if i.val < 95 then 41 else 68))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 41 else 38) else (if i.val < 99 then 38 else 38)) else (if i.val < 102 then (if i.val < 101 then 74 else 21) else (if i.val < 103 then 42 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 73 else 21) else (if i.val < 107 then 22 else 38)) else (if i.val < 110 then (if i.val < 109 then 38 else 38) else (if i.val < 111 then 73 else 75)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 21 else 38) else (if i.val < 115 then 38 else 38)) else (if i.val < 118 then (if i.val < 117 then 21 else 22) else (if i.val < 119 then 21 else 38))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 21 else 43) else (if i.val < 123 then 38 else 38)) else (if i.val < 126 then (if i.val < 125 then 38 else 21) else (if i.val < 127 then 38 else 38))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 68 else 7) else (if i.val < 131 then 71 else 68)) else (if i.val < 134 then (if i.val < 133 then 40 else 41) else (if i.val < 135 then 41 else 21))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 38 else 73) else (if i.val < 139 then 21 else 70)) else (if i.val < 142 then (if i.val < 141 then 41 else 38) else (if i.val < 143 then 21 else 68)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 41 else 21) else (if i.val < 147 then 39 else 68)) else (if i.val < 150 then (if i.val < 149 then 38 else 38) else (if i.val < 151 then 38 else 38))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 22 else 21) else (if i.val < 155 then 22 else 41)) else (if i.val < 158 then (if i.val < 157 then 73 else 38) else (if i.val < 159 then 38 else 38))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 38 else 38) else (if i.val < 163 then 20 else 21)) else (if i.val < 166 then (if i.val < 165 then 38 else 21) else (if i.val < 167 then 21 else 21))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 38 else 20) else (if i.val < 171 then 73 else 21)) else (if i.val < 174 then (if i.val < 173 then 38 else 21) else (if i.val < 175 then 41 else 73)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 38) else (if i.val < 179 then 41 else 38)) else (if i.val < 182 then (if i.val < 181 then 38 else 21) else (if i.val < 183 then 21 else 21))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 38 else 38) else (if i.val < 187 then 71 else 38)) else (if i.val < 190 then (if i.val < 189 then 39 else 22) else (if i.val < 191 then 22 else 22)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 21 else 38) else (if i.val < 195 then 21 else 21)) else (if i.val < 198 then (if i.val < 197 then 21 else 38) else (if i.val < 199 then 74 else 38))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 41 else 38) else (if i.val < 203 then 21 else 40)) else (if i.val < 206 then (if i.val < 205 then 38 else 7) else (if i.val < 207 then 22 else 75)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 22 else 20) else (if i.val < 211 then 21 else 40)) else (if i.val < 214 then (if i.val < 213 then 21 else 21) else (if i.val < 215 then 21 else 21))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 73 else 22) else (if i.val < 219 then 22 else 21)) else (if i.val < 222 then (if i.val < 221 then 38 else 7) else (if i.val < 223 then 68 else 38))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 21 else 21) else (if i.val < 227 then 72 else 38)) else (if i.val < 230 then (if i.val < 229 then 21 else 21) else (if i.val < 231 then 43 else 21))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 38 else 38) else (if i.val < 235 then 38 else 21)) else (if i.val < 238 then (if i.val < 237 then 38 else 38) else (if i.val < 239 then 73 else 42)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 21 else 43) else (if i.val < 243 then 20 else 22)) else (if i.val < 246 then (if i.val < 245 then 21 else 38) else (if i.val < 247 then 38 else 21))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 38 else 71) else (if i.val < 251 then 22 else 38)) else (if i.val < 254 then (if i.val < 253 then 21 else 38) else (if i.val < 255 then 38 else 38))))))))

theorem g32p_supplierForest_actual_135 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_135 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_135 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_050601
  · exact g32p_supplierForest_actual_050602
  · exact g32p_supplierForest_actual_050635
  · exact g32p_supplierForest_actual_050682
  · exact g32p_supplierForest_actual_050710
  · exact g32p_supplierForest_actual_050726
  · exact g32p_supplierForest_actual_050765
  · exact g32p_supplierForest_actual_050817
  · exact g32p_supplierForest_actual_050846
  · exact g32p_supplierForest_actual_050874
  · exact g32p_supplierForest_actual_050881
  · exact g32p_supplierForest_actual_051034
  · exact g32p_supplierForest_actual_051191
  · exact g32p_supplierForest_actual_051196
  · exact g32p_supplierForest_actual_051267
  · exact g32p_supplierForest_actual_051294
  · exact g32p_supplierForest_actual_051406
  · exact g32p_supplierForest_actual_051451
  · exact g32p_supplierForest_actual_051462
  · exact g32p_supplierForest_actual_051609
  · exact g32p_supplierForest_actual_051628
  · exact g32p_supplierForest_actual_051645
  · exact g32p_supplierForest_actual_051696
  · exact g32p_supplierForest_actual_051761
  · exact g32p_supplierForest_actual_051812
  · exact g32p_supplierForest_actual_051833
  · exact g32p_supplierForest_actual_051977
  · exact g32p_supplierForest_actual_051993
  · exact g32p_supplierForest_actual_052096
  · exact g32p_supplierForest_actual_052108
  · exact g32p_supplierForest_actual_052112
  · exact g32p_supplierForest_actual_052117
  · exact g32p_supplierForest_actual_052134
  · exact g32p_supplierForest_actual_052192
  · exact g32p_supplierForest_actual_052193
  · exact g32p_supplierForest_actual_052216
  · exact g32p_supplierForest_actual_052285
  · exact g32p_supplierForest_actual_052290
  · exact g32p_supplierForest_actual_052360
  · exact g32p_supplierForest_actual_052461
  · exact g32p_supplierForest_actual_052483
  · exact g32p_supplierForest_actual_052571
  · exact g32p_supplierForest_actual_052586
  · exact g32p_supplierForest_actual_052614
  · exact g32p_supplierForest_actual_052646
  · exact g32p_supplierForest_actual_052686
  · exact g32p_supplierForest_actual_052692
  · exact g32p_supplierForest_actual_052767
  · exact g32p_supplierForest_actual_052785
  · exact g32p_supplierForest_actual_052796
  · exact g32p_supplierForest_actual_052850
  · exact g32p_supplierForest_actual_052883
  · exact g32p_supplierForest_actual_052938
  · exact g32p_supplierForest_actual_052942
  · exact g32p_supplierForest_actual_052953
  · exact g32p_supplierForest_actual_052963
  · exact g32p_supplierForest_actual_053066
  · exact g32p_supplierForest_actual_053139
  · exact g32p_supplierForest_actual_053160
  · exact g32p_supplierForest_actual_053239
  · exact g32p_supplierForest_actual_053257
  · exact g32p_supplierForest_actual_053332
  · exact g32p_supplierForest_actual_053355
  · exact g32p_supplierForest_actual_053378
  · exact g32p_supplierForest_actual_053401
  · exact g32p_supplierForest_actual_053436
  · exact g32p_supplierForest_actual_053449
  · exact g32p_supplierForest_actual_053466
  · exact g32p_supplierForest_actual_053502
  · exact g32p_supplierForest_actual_053504
  · exact g32p_supplierForest_actual_053543
  · exact g32p_supplierForest_actual_053630
  · exact g32p_supplierForest_actual_053675
  · exact g32p_supplierForest_actual_053741
  · exact g32p_supplierForest_actual_053755
  · exact g32p_supplierForest_actual_053816
  · exact g32p_supplierForest_actual_054021
  · exact g32p_supplierForest_actual_054175
  · exact g32p_supplierForest_actual_054267
  · exact g32p_supplierForest_actual_054339
  · exact g32p_supplierForest_actual_054344
  · exact g32p_supplierForest_actual_054353
  · exact g32p_supplierForest_actual_054479
  · exact g32p_supplierForest_actual_054553
  · exact g32p_supplierForest_actual_054561
  · exact g32p_supplierForest_actual_054599
  · exact g32p_supplierForest_actual_054668
  · exact g32p_supplierForest_actual_054680
  · exact g32p_supplierForest_actual_054742
  · exact g32p_supplierForest_actual_054786
  · exact g32p_supplierForest_actual_054869
  · exact g32p_supplierForest_actual_054953
  · exact g32p_supplierForest_actual_055038
  · exact g32p_supplierForest_actual_055043
  · exact g32p_supplierForest_actual_055092
  · exact g32p_supplierForest_actual_055419
  · exact g32p_supplierForest_actual_055490
  · exact g32p_supplierForest_actual_055528
  · exact g32p_supplierForest_actual_055546
  · exact g32p_supplierForest_actual_055550
  · exact g32p_supplierForest_actual_055637
  · exact g32p_supplierForest_actual_055665
  · exact g32p_supplierForest_actual_055677
  · exact g32p_supplierForest_actual_055696
  · exact g32p_supplierForest_actual_055858
  · exact g32p_supplierForest_actual_055861
  · exact g32p_supplierForest_actual_055892
  · exact g32p_supplierForest_actual_055931
  · exact g32p_supplierForest_actual_055933
  · exact g32p_supplierForest_actual_055958
  · exact g32p_supplierForest_actual_056056
  · exact g32p_supplierForest_actual_056057
  · exact g32p_supplierForest_actual_056228
  · exact g32p_supplierForest_actual_056284
  · exact g32p_supplierForest_actual_056317
  · exact g32p_supplierForest_actual_056351
  · exact g32p_supplierForest_actual_056396
  · exact g32p_supplierForest_actual_056397
  · exact g32p_supplierForest_actual_056440
  · exact g32p_supplierForest_actual_056467
  · exact g32p_supplierForest_actual_056470
  · exact g32p_supplierForest_actual_056518
  · exact g32p_supplierForest_actual_056536
  · exact g32p_supplierForest_actual_056624
  · exact g32p_supplierForest_actual_056695
  · exact g32p_supplierForest_actual_056778
  · exact g32p_supplierForest_actual_056895
  · exact g32p_supplierForest_actual_056950
  · exact g32p_supplierForest_actual_057021
  · exact g32p_supplierForest_actual_057078
  · exact g32p_supplierForest_actual_057114
  · exact g32p_supplierForest_actual_057476
  · exact g32p_supplierForest_actual_057486
  · exact g32p_supplierForest_actual_057524
  · exact g32p_supplierForest_actual_057540
  · exact g32p_supplierForest_actual_057589
  · exact g32p_supplierForest_actual_057773
  · exact g32p_supplierForest_actual_058021
  · exact g32p_supplierForest_actual_058120
  · exact g32p_supplierForest_actual_058184
  · exact g32p_supplierForest_actual_058220
  · exact g32p_supplierForest_actual_058283
  · exact g32p_supplierForest_actual_058372
  · exact g32p_supplierForest_actual_058432
  · exact g32p_supplierForest_actual_058440
  · exact g32p_supplierForest_actual_058476
  · exact g32p_supplierForest_actual_058498
  · exact g32p_supplierForest_actual_058542
  · exact g32p_supplierForest_actual_058572
  · exact g32p_supplierForest_actual_058591
  · exact g32p_supplierForest_actual_058600
  · exact g32p_supplierForest_actual_058613
  · exact g32p_supplierForest_actual_058632
  · exact g32p_supplierForest_actual_058740
  · exact g32p_supplierForest_actual_058742
  · exact g32p_supplierForest_actual_058765
  · exact g32p_supplierForest_actual_058776
  · exact g32p_supplierForest_actual_058862
  · exact g32p_supplierForest_actual_058875
  · exact g32p_supplierForest_actual_058906
  · exact g32p_supplierForest_actual_058971
  · exact g32p_supplierForest_actual_059000
  · exact g32p_supplierForest_actual_059037
  · exact g32p_supplierForest_actual_059147
  · exact g32p_supplierForest_actual_059153
  · exact g32p_supplierForest_actual_059165
  · exact g32p_supplierForest_actual_059267
  · exact g32p_supplierForest_actual_059432
  · exact g32p_supplierForest_actual_059439
  · exact g32p_supplierForest_actual_059467
  · exact g32p_supplierForest_actual_059712
  · exact g32p_supplierForest_actual_059833
  · exact g32p_supplierForest_actual_059853
  · exact g32p_supplierForest_actual_059895
  · exact g32p_supplierForest_actual_059929
  · exact g32p_supplierForest_actual_059937
  · exact g32p_supplierForest_actual_059942
  · exact g32p_supplierForest_actual_059949
  · exact g32p_supplierForest_actual_059971
  · exact g32p_supplierForest_actual_059981
  · exact g32p_supplierForest_actual_060002
  · exact g32p_supplierForest_actual_060020
  · exact g32p_supplierForest_actual_060107
  · exact g32p_supplierForest_actual_060138
  · exact g32p_supplierForest_actual_060199
  · exact g32p_supplierForest_actual_060216
  · exact g32p_supplierForest_actual_060335
  · exact g32p_supplierForest_actual_060369
  · exact g32p_supplierForest_actual_060524
  · exact g32p_supplierForest_actual_060607
  · exact g32p_supplierForest_actual_060649
  · exact g32p_supplierForest_actual_060807
  · exact g32p_supplierForest_actual_060908
  · exact g32p_supplierForest_actual_060958
  · exact g32p_supplierForest_actual_060997
  · exact g32p_supplierForest_actual_061022
  · exact g32p_supplierForest_actual_061045
  · exact g32p_supplierForest_actual_061058
  · exact g32p_supplierForest_actual_061174
  · exact g32p_supplierForest_actual_061220
  · exact g32p_supplierForest_actual_061356
  · exact g32p_supplierForest_actual_061406
  · exact g32p_supplierForest_actual_061494
  · exact g32p_supplierForest_actual_061530
  · exact g32p_supplierForest_actual_061561
  · exact g32p_supplierForest_actual_061567
  · exact g32p_supplierForest_actual_061591
  · exact g32p_supplierForest_actual_061649
  · exact g32p_supplierForest_actual_061700
  · exact g32p_supplierForest_actual_061711
  · exact g32p_supplierForest_actual_061724
  · exact g32p_supplierForest_actual_061772
  · exact g32p_supplierForest_actual_061816
  · exact g32p_supplierForest_actual_061817
  · exact g32p_supplierForest_actual_061850
  · exact g32p_supplierForest_actual_061872
  · exact g32p_supplierForest_actual_061923
  · exact g32p_supplierForest_actual_062070
  · exact g32p_supplierForest_actual_062086
  · exact g32p_supplierForest_actual_062195
  · exact g32p_supplierForest_actual_062323
  · exact g32p_supplierForest_actual_062544
  · exact g32p_supplierForest_actual_062555
  · exact g32p_supplierForest_actual_062567
  · exact g32p_supplierForest_actual_062576
  · exact g32p_supplierForest_actual_062609
  · exact g32p_supplierForest_actual_062892
  · exact g32p_supplierForest_actual_062924
  · exact g32p_supplierForest_actual_062937
  · exact g32p_supplierForest_actual_063003
  · exact g32p_supplierForest_actual_063026
  · exact g32p_supplierForest_actual_063095
  · exact g32p_supplierForest_actual_063125
  · exact g32p_supplierForest_actual_063153
  · exact g32p_supplierForest_actual_063217
  · exact g32p_supplierForest_actual_063278
  · exact g32p_supplierForest_actual_063281
  · exact g32p_supplierForest_actual_063371
  · exact g32p_supplierForest_actual_063398
  · exact g32p_supplierForest_actual_063399
  · exact g32p_supplierForest_actual_063699
  · exact g32p_supplierForest_actual_063792
  · exact g32p_supplierForest_actual_063857
  · exact g32p_supplierForest_actual_063878
  · exact g32p_supplierForest_actual_063938
  · exact g32p_supplierForest_actual_063978
  · exact g32p_supplierForest_actual_064020
  · exact g32p_supplierForest_actual_064036
  · exact g32p_supplierForest_actual_064103
  · exact g32p_supplierForest_actual_064157
  · exact g32p_supplierForest_actual_064284
  · exact g32p_supplierForest_actual_064357
  · exact g32p_supplierForest_actual_064405
  · exact g32p_supplierForest_actual_064408
  · exact g32p_supplierForest_actual_064421
  · exact g32p_supplierForest_actual_064440

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_064466 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_064466 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064466 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_052949 := by
  decide +kernel

theorem g32p_supplierForest_actual_064466 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064466) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_064466
    g32p_supplierForest_actual_052949

def g32p_supplierForest_node_064471 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_064471 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064471 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063234 := by
  decide +kernel

theorem g32p_supplierForest_actual_064471 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064471) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_064471
    g32p_supplierForest_actual_063234

def g32p_supplierForest_node_064494 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064494 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064494 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064496 := by
  decide +kernel

theorem g32p_supplierForest_actual_064494 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064494) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_064494
    g32p_supplierForest_actual_064496

def g32p_supplierForest_node_064521 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064521 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064521 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053489 := by
  decide +kernel

theorem g32p_supplierForest_actual_064521 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064521) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_064521
    g32p_supplierForest_actual_053489

def g32p_supplierForest_node_064540 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064540 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064540 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_049125 := by
  decide +kernel

theorem g32p_supplierForest_actual_064540 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064540) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_064540
    g32p_supplierForest_actual_049125

def g32p_supplierForest_node_064543 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064543 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_052811 := by
  decide +kernel

theorem g32p_supplierForest_actual_064543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064543) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 3 g32p_supplierForest_edge_064543
    g32p_supplierForest_actual_052811

def g32p_supplierForest_node_064549 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064549 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064549 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_138185 := by
  decide +kernel

theorem g32p_supplierForest_actual_064549 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064549) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_064549
    g32p_supplierForest_actual_138185

def g32p_supplierForest_node_064560 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064560 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064560 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070004 := by
  decide +kernel

theorem g32p_supplierForest_actual_064560 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064560) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 2 g32p_supplierForest_edge_064560
    g32p_supplierForest_actual_070004

def g32p_supplierForest_node_064580 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064580 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064580 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063221 := by
  decide +kernel

theorem g32p_supplierForest_actual_064580 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064580) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_064580
    g32p_supplierForest_actual_063221

def g32p_supplierForest_node_064665 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064665 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064665 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065890 := by
  decide +kernel

theorem g32p_supplierForest_actual_064665 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064665) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_064665
    g32p_supplierForest_actual_065890

def g32p_supplierForest_node_064683 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064683 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064683 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_050949 := by
  decide +kernel

theorem g32p_supplierForest_actual_064683 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064683) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_064683
    g32p_supplierForest_actual_050949

def g32p_supplierForest_node_064713 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064713 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064713 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_129209 := by
  decide +kernel

theorem g32p_supplierForest_actual_064713 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064713) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_064713
    g32p_supplierForest_actual_129209

def g32p_supplierForest_node_064731 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064731 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064731 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057578 := by
  decide +kernel

theorem g32p_supplierForest_actual_064731 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064731) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_064731
    g32p_supplierForest_actual_057578

def g32p_supplierForest_node_064737 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064737 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064737 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066966 := by
  decide +kernel

theorem g32p_supplierForest_actual_064737 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064737) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 1 g32p_supplierForest_edge_064737
    g32p_supplierForest_actual_066966

def g32p_supplierForest_node_064773 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_064773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064773 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067021 := by
  decide +kernel

theorem g32p_supplierForest_actual_064773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064773) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_064773
    g32p_supplierForest_actual_067021

def g32p_supplierForest_node_064849 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064849 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064849 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067178 := by
  decide +kernel

theorem g32p_supplierForest_actual_064849 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064849) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_064849
    g32p_supplierForest_actual_067178

def g32p_supplierForest_node_064888 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_064888 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064888 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061776 := by
  decide +kernel

theorem g32p_supplierForest_actual_064888 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064888) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_064888
    g32p_supplierForest_actual_061776

def g32p_supplierForest_node_064889 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_064889 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064889 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_064787 := by
  decide +kernel

theorem g32p_supplierForest_actual_064889 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064889) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_064889
    g32p_supplierForest_actual_064787

def g32p_supplierForest_node_064921 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064921 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064921 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127836 := by
  decide +kernel

theorem g32p_supplierForest_actual_064921 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064921) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_064921
    g32p_supplierForest_actual_127836

def g32p_supplierForest_node_064981 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_064981 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064981 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_066519 := by
  decide +kernel

theorem g32p_supplierForest_actual_064981 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064981) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_064981
    g32p_supplierForest_actual_066519

def g32p_supplierForest_node_064997 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064997 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064997 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131950 := by
  decide +kernel

theorem g32p_supplierForest_actual_064997 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064997) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_064997
    g32p_supplierForest_actual_131950

def g32p_supplierForest_node_065156 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_065156 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065156 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_130896 := by
  decide +kernel

theorem g32p_supplierForest_actual_065156 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065156) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_065156
    g32p_supplierForest_actual_130896

def g32p_supplierForest_node_065168 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065168 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065168 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130892 := by
  decide +kernel

theorem g32p_supplierForest_actual_065168 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065168) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_065168
    g32p_supplierForest_actual_130892

def g32p_supplierForest_node_065170 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065170 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067804 := by
  decide +kernel

theorem g32p_supplierForest_actual_065170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065170) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065170
    g32p_supplierForest_actual_067804

def g32p_supplierForest_node_065411 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065411 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065411 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_010147 := by
  decide +kernel

theorem g32p_supplierForest_actual_065411 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065411) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_065411
    g32p_supplierForest_actual_010147

def g32p_supplierForest_node_065445 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_065445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065445 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064337 := by
  decide +kernel

theorem g32p_supplierForest_actual_065445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065445) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_065445
    g32p_supplierForest_actual_064337

def g32p_supplierForest_node_065455 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065455 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065455 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063209 := by
  decide +kernel

theorem g32p_supplierForest_actual_065455 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065455) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_065455
    g32p_supplierForest_actual_063209

def g32p_supplierForest_node_065489 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065489 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065489 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011287 := by
  decide +kernel

theorem g32p_supplierForest_actual_065489 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065489) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_065489
    g32p_supplierForest_actual_011287

def g32p_supplierForest_node_065512 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065512 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065512 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_057512 := by
  decide +kernel

theorem g32p_supplierForest_actual_065512 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065512) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_065512
    g32p_supplierForest_actual_057512

def g32p_supplierForest_node_065547 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_065547 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065547 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_010272 := by
  decide +kernel

theorem g32p_supplierForest_actual_065547 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065547) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_065547
    g32p_supplierForest_actual_010272

def g32p_supplierForest_node_065630 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065630 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065630 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131125 := by
  decide +kernel

theorem g32p_supplierForest_actual_065630 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065630) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_065630
    g32p_supplierForest_actual_131125

def g32p_supplierForest_node_065805 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065805 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065805 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_047135 := by
  decide +kernel

theorem g32p_supplierForest_actual_065805 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065805) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_065805
    g32p_supplierForest_actual_047135

def g32p_supplierForest_node_065834 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065834 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065834 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065262 := by
  decide +kernel

theorem g32p_supplierForest_actual_065834 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065834) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_065834
    g32p_supplierForest_actual_065262

def g32p_supplierForest_node_065907 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_065907 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065907 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068703 := by
  decide +kernel

theorem g32p_supplierForest_actual_065907 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065907) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_065907
    g32p_supplierForest_actual_068703

def g32p_supplierForest_node_065991 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065991 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_060415 := by
  decide +kernel

theorem g32p_supplierForest_actual_065991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065991) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_065991
    g32p_supplierForest_actual_060415

def g32p_supplierForest_node_066090 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066090 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066090 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069296 := by
  decide +kernel

theorem g32p_supplierForest_actual_066090 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066090) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_066090
    g32p_supplierForest_actual_069296

def g32p_supplierForest_node_066100 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066100 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066100 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132889 := by
  decide +kernel

theorem g32p_supplierForest_actual_066100 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066100) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_066100
    g32p_supplierForest_actual_132889

def g32p_supplierForest_node_066104 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066104 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066104 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065319 := by
  decide +kernel

theorem g32p_supplierForest_actual_066104 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066104) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_066104
    g32p_supplierForest_actual_065319

def g32p_supplierForest_node_066152 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066152 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066152 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068763 := by
  decide +kernel

theorem g32p_supplierForest_actual_066152 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066152) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_066152
    g32p_supplierForest_actual_068763

def g32p_supplierForest_node_066188 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066188 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066188 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057947 := by
  decide +kernel

theorem g32p_supplierForest_actual_066188 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066188) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_066188
    g32p_supplierForest_actual_057947

def g32p_supplierForest_node_066237 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066237 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066237 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_140767 := by
  decide +kernel

theorem g32p_supplierForest_actual_066237 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066237) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_066237
    g32p_supplierForest_actual_140767

def g32p_supplierForest_node_066251 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066251 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066251 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065362 := by
  decide +kernel

theorem g32p_supplierForest_actual_066251 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066251) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_066251
    g32p_supplierForest_actual_065362

def g32p_supplierForest_node_066268 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066268 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066268 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_051479 := by
  decide +kernel

theorem g32p_supplierForest_actual_066268 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066268) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_066268
    g32p_supplierForest_actual_051479

def g32p_supplierForest_node_066281 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066281 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066281 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_066257 := by
  decide +kernel

theorem g32p_supplierForest_actual_066281 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066281) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 3 g32p_supplierForest_edge_066281
    g32p_supplierForest_actual_066257

def g32p_supplierForest_node_066345 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066345 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066345 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_142165 := by
  decide +kernel

theorem g32p_supplierForest_actual_066345 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066345) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 3 g32p_supplierForest_edge_066345
    g32p_supplierForest_actual_142165

def g32p_supplierForest_node_066361 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066361 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066361 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_141222 := by
  decide +kernel

theorem g32p_supplierForest_actual_066361 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066361) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_066361
    g32p_supplierForest_actual_141222

def g32p_supplierForest_node_066382 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066382 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066382 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_047477 := by
  decide +kernel

theorem g32p_supplierForest_actual_066382 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066382) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_066382
    g32p_supplierForest_actual_047477

def g32p_supplierForest_node_066710 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066710 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066710 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_008814 := by
  decide +kernel

theorem g32p_supplierForest_actual_066710 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066710) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_066710
    g32p_supplierForest_actual_008814

def g32p_supplierForest_node_066778 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066778 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066778 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048777 := by
  decide +kernel

theorem g32p_supplierForest_actual_066778 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066778) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_066778
    g32p_supplierForest_actual_048777

def g32p_supplierForest_node_066790 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066790 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066790 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047747 := by
  decide +kernel

theorem g32p_supplierForest_actual_066790 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066790) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 3 g32p_supplierForest_edge_066790
    g32p_supplierForest_actual_047747

def g32p_supplierForest_node_066875 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066875 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066875 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_133844 := by
  decide +kernel

theorem g32p_supplierForest_actual_066875 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066875) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_066875
    g32p_supplierForest_actual_133844

def g32p_supplierForest_node_066884 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066884 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066884 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_064867 := by
  decide +kernel

theorem g32p_supplierForest_actual_066884 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066884) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_066884
    g32p_supplierForest_actual_064867

def g32p_supplierForest_node_066907 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066907 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066907 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071197 := by
  decide +kernel

theorem g32p_supplierForest_actual_066907 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066907) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_066907
    g32p_supplierForest_actual_071197

def g32p_supplierForest_node_066965 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066965 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_011987 := by
  decide +kernel

theorem g32p_supplierForest_actual_066965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066965) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_066965
    g32p_supplierForest_actual_011987

def g32p_supplierForest_node_067107 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067107 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067107 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070195 := by
  decide +kernel

theorem g32p_supplierForest_actual_067107 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067107) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_067107
    g32p_supplierForest_actual_070195

def g32p_supplierForest_node_067166 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067166 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_049560 := by
  decide +kernel

theorem g32p_supplierForest_actual_067166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067166) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_067166
    g32p_supplierForest_actual_049560

def g32p_supplierForest_node_067179 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067179 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067179 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010059 := by
  decide +kernel

theorem g32p_supplierForest_actual_067179 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067179) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_067179
    g32p_supplierForest_actual_010059

def g32p_supplierForest_node_067277 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067277 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067277 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_045128 := by
  decide +kernel

theorem g32p_supplierForest_actual_067277 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067277) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_067277
    g32p_supplierForest_actual_045128

def g32p_supplierForest_node_067319 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067319 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061713 := by
  decide +kernel

theorem g32p_supplierForest_actual_067319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067319) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_067319
    g32p_supplierForest_actual_061713

def g32p_supplierForest_node_067334 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_067334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067334 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064168 := by
  decide +kernel

theorem g32p_supplierForest_actual_067334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067334) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_067334
    g32p_supplierForest_actual_064168

def g32p_supplierForest_node_067341 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067341 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_054658 := by
  decide +kernel

theorem g32p_supplierForest_actual_067341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067341) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_067341
    g32p_supplierForest_actual_054658

def g32p_supplierForest_node_067342 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067342 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067342 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055151 := by
  decide +kernel

theorem g32p_supplierForest_actual_067342 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067342) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_067342
    g32p_supplierForest_actual_055151

def g32p_supplierForest_node_067376 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067376 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067376 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_140197 := by
  decide +kernel

theorem g32p_supplierForest_actual_067376 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067376) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_067376
    g32p_supplierForest_actual_140197

def g32p_supplierForest_node_067420 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067420 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067420 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_048041 := by
  decide +kernel

theorem g32p_supplierForest_actual_067420 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067420) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_067420
    g32p_supplierForest_actual_048041

def g32p_supplierForest_node_067447 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067447 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067447 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131098 := by
  decide +kernel

theorem g32p_supplierForest_actual_067447 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067447) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_067447
    g32p_supplierForest_actual_131098

def g32p_supplierForest_node_067478 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067478 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067478 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060742 := by
  decide +kernel

theorem g32p_supplierForest_actual_067478 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067478) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_067478
    g32p_supplierForest_actual_060742

def g32p_supplierForest_node_067518 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067518 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067518 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060847 := by
  decide +kernel

theorem g32p_supplierForest_actual_067518 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067518) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_067518
    g32p_supplierForest_actual_060847

def g32p_supplierForest_node_067531 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067531 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053533 := by
  decide +kernel

theorem g32p_supplierForest_actual_067531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067531) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_067531
    g32p_supplierForest_actual_053533

def g32p_supplierForest_node_067672 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067672 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067672 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_062835 := by
  decide +kernel

theorem g32p_supplierForest_actual_067672 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067672) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_067672
    g32p_supplierForest_actual_062835

def g32p_supplierForest_node_067809 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067809 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067809 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061535 := by
  decide +kernel

theorem g32p_supplierForest_actual_067809 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067809) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_067809
    g32p_supplierForest_actual_061535

def g32p_supplierForest_node_068024 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068024 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068024 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_066831 := by
  decide +kernel

theorem g32p_supplierForest_actual_068024 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068024) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_068024
    g32p_supplierForest_actual_066831

def g32p_supplierForest_node_068037 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_068037 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068037 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064574 := by
  decide +kernel

theorem g32p_supplierForest_actual_068037 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068037) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_068037
    g32p_supplierForest_actual_064574

def g32p_supplierForest_node_068117 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068117 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068117 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_059523 := by
  decide +kernel

theorem g32p_supplierForest_actual_068117 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068117) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_068117
    g32p_supplierForest_actual_059523

def g32p_supplierForest_node_068482 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068482 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068482 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_136775 := by
  decide +kernel

theorem g32p_supplierForest_actual_068482 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068482) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_068482
    g32p_supplierForest_actual_136775

def g32p_supplierForest_node_068513 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068513 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068513 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045209 := by
  decide +kernel

theorem g32p_supplierForest_actual_068513 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068513) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_068513
    g32p_supplierForest_actual_045209

def g32p_supplierForest_node_068707 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068707 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068707 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_060827 := by
  decide +kernel

theorem g32p_supplierForest_actual_068707 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068707) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_068707
    g32p_supplierForest_actual_060827

def g32p_supplierForest_node_068722 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068722 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068722 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_010619 := by
  decide +kernel

theorem g32p_supplierForest_actual_068722 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068722) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_068722
    g32p_supplierForest_actual_010619

def g32p_supplierForest_node_068738 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068738 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_049445 := by
  decide +kernel

theorem g32p_supplierForest_actual_068738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068738) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_068738
    g32p_supplierForest_actual_049445

def g32p_supplierForest_node_068788 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_068788 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068788 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_050241 := by
  decide +kernel

theorem g32p_supplierForest_actual_068788 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068788) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_068788
    g32p_supplierForest_actual_050241

def g32p_supplierForest_node_068792 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068792 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068792 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_059862 := by
  decide +kernel

theorem g32p_supplierForest_actual_068792 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068792) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_068792
    g32p_supplierForest_actual_059862

def g32p_supplierForest_node_068835 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068835 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068835 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_135158 := by
  decide +kernel

theorem g32p_supplierForest_actual_068835 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068835) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_068835
    g32p_supplierForest_actual_135158

def g32p_supplierForest_node_068884 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068884 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068884 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_069197 := by
  decide +kernel

theorem g32p_supplierForest_actual_068884 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068884) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_068884
    g32p_supplierForest_actual_069197

def g32p_supplierForest_node_068898 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068898 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068898 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063891 := by
  decide +kernel

theorem g32p_supplierForest_actual_068898 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068898) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_068898
    g32p_supplierForest_actual_063891

def g32p_supplierForest_node_068903 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068903 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068903 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067029 := by
  decide +kernel

theorem g32p_supplierForest_actual_068903 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068903) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_068903
    g32p_supplierForest_actual_067029

def g32p_supplierForest_node_068998 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068998 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068998 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_049222 := by
  decide +kernel

theorem g32p_supplierForest_actual_068998 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068998) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_068998
    g32p_supplierForest_actual_049222

def g32p_supplierForest_node_069030 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069030 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069030 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_064857 := by
  decide +kernel

theorem g32p_supplierForest_actual_069030 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069030) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_069030
    g32p_supplierForest_actual_064857

def g32p_supplierForest_node_069095 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069095 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068720 := by
  decide +kernel

theorem g32p_supplierForest_actual_069095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069095) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_069095
    g32p_supplierForest_actual_068720

def g32p_supplierForest_node_069113 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_069113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069113 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070147 := by
  decide +kernel

theorem g32p_supplierForest_actual_069113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069113) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_069113
    g32p_supplierForest_actual_070147

def g32p_supplierForest_node_069136 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069136 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069136 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068791 := by
  decide +kernel

theorem g32p_supplierForest_actual_069136 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069136) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_069136
    g32p_supplierForest_actual_068791

def g32p_supplierForest_node_069158 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_069158 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069158 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_056202 := by
  decide +kernel

theorem g32p_supplierForest_actual_069158 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069158) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_069158
    g32p_supplierForest_actual_056202

def g32p_supplierForest_node_069183 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_069183 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069183 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_133524 := by
  decide +kernel

theorem g32p_supplierForest_actual_069183 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069183) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_069183
    g32p_supplierForest_actual_133524

def g32p_supplierForest_node_069221 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069221 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069221 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055186 := by
  decide +kernel

theorem g32p_supplierForest_actual_069221 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069221) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_069221
    g32p_supplierForest_actual_055186

def g32p_supplierForest_node_069273 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_069273 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069273 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_049201 := by
  decide +kernel

theorem g32p_supplierForest_actual_069273 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069273) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_069273
    g32p_supplierForest_actual_049201

def g32p_supplierForest_node_069294 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069294 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069294 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_058753 := by
  decide +kernel

theorem g32p_supplierForest_actual_069294 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069294) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_069294
    g32p_supplierForest_actual_058753

def g32p_supplierForest_node_069308 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_069308 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069308 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010708 := by
  decide +kernel

theorem g32p_supplierForest_actual_069308 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069308) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_069308
    g32p_supplierForest_actual_010708

def g32p_supplierForest_node_069382 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_069382 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069382 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060825 := by
  decide +kernel

theorem g32p_supplierForest_actual_069382 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069382) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_069382
    g32p_supplierForest_actual_060825

def g32p_supplierForest_node_069397 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069397 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069397 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067079 := by
  decide +kernel

theorem g32p_supplierForest_actual_069397 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069397) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_069397
    g32p_supplierForest_actual_067079

def g32p_supplierForest_node_069414 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069414 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069414 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_054591 := by
  decide +kernel

theorem g32p_supplierForest_actual_069414 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069414) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_069414
    g32p_supplierForest_actual_054591

def g32p_supplierForest_node_069625 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069625 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069625 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_135694 := by
  decide +kernel

theorem g32p_supplierForest_actual_069625 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069625) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_069625
    g32p_supplierForest_actual_135694

def g32p_supplierForest_node_069741 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_069741 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069741 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_069667 := by
  decide +kernel

theorem g32p_supplierForest_actual_069741 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069741) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_069741
    g32p_supplierForest_actual_069667

def g32p_supplierForest_node_069749 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069749 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069749 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067738 := by
  decide +kernel

theorem g32p_supplierForest_actual_069749 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069749) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_069749
    g32p_supplierForest_actual_067738

def g32p_supplierForest_node_069768 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_069768 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069768 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070880 := by
  decide +kernel

theorem g32p_supplierForest_actual_069768 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069768) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_069768
    g32p_supplierForest_actual_070880

def g32p_supplierForest_node_069878 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_069878 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069878 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_052092 := by
  decide +kernel

theorem g32p_supplierForest_actual_069878 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069878) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_069878
    g32p_supplierForest_actual_052092

def g32p_supplierForest_node_069888 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069888 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069888 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071164 := by
  decide +kernel

theorem g32p_supplierForest_actual_069888 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069888) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_069888
    g32p_supplierForest_actual_071164

def g32p_supplierForest_node_070009 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_070009 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070009 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_143817 := by
  decide +kernel

theorem g32p_supplierForest_actual_070009 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070009) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_070009
    g32p_supplierForest_actual_143817

def g32p_supplierForest_node_070046 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_070046 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070046 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064120 := by
  decide +kernel

theorem g32p_supplierForest_actual_070046 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070046) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_070046
    g32p_supplierForest_actual_064120

def g32p_supplierForest_node_070091 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070091 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_138500 := by
  decide +kernel

theorem g32p_supplierForest_actual_070091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070091) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_070091
    g32p_supplierForest_actual_138500

def g32p_supplierForest_node_070123 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070123 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070123 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071650 := by
  decide +kernel

theorem g32p_supplierForest_actual_070123 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070123) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_070123
    g32p_supplierForest_actual_071650

def g32p_supplierForest_node_070129 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070129 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070129 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_057522 := by
  decide +kernel

theorem g32p_supplierForest_actual_070129 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070129) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_070129
    g32p_supplierForest_actual_057522

def g32p_supplierForest_node_070200 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070200 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070200 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059264 := by
  decide +kernel

theorem g32p_supplierForest_actual_070200 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070200) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_070200
    g32p_supplierForest_actual_059264

def g32p_supplierForest_node_070211 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_070211 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070211 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_046502 := by
  decide +kernel

theorem g32p_supplierForest_actual_070211 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070211) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_070211
    g32p_supplierForest_actual_046502

def g32p_supplierForest_node_070323 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_070323 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070323 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047806 := by
  decide +kernel

theorem g32p_supplierForest_actual_070323 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070323) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_070323
    g32p_supplierForest_actual_047806

def g32p_supplierForest_node_070353 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070353 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070353 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_136230 := by
  decide +kernel

theorem g32p_supplierForest_actual_070353 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070353) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_070353
    g32p_supplierForest_actual_136230

def g32p_supplierForest_node_070380 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070380 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070380 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_136121 := by
  decide +kernel

theorem g32p_supplierForest_actual_070380 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070380) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 1 g32p_supplierForest_edge_070380
    g32p_supplierForest_actual_136121

def g32p_supplierForest_node_070436 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_070436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070436 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_134106 := by
  decide +kernel

theorem g32p_supplierForest_actual_070436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070436) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_070436
    g32p_supplierForest_actual_134106

def g32p_supplierForest_node_070485 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_070485 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070485 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_049008 := by
  decide +kernel

theorem g32p_supplierForest_actual_070485 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070485) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_070485
    g32p_supplierForest_actual_049008

def g32p_supplierForest_node_070630 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070630 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070630 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053372 := by
  decide +kernel

theorem g32p_supplierForest_actual_070630 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070630) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_070630
    g32p_supplierForest_actual_053372

def g32p_supplierForest_node_070638 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_070638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070638 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_128199 := by
  decide +kernel

theorem g32p_supplierForest_actual_070638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070638) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_070638
    g32p_supplierForest_actual_128199

def g32p_supplierForest_node_070853 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_070853 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070853 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_136596 := by
  decide +kernel

theorem g32p_supplierForest_actual_070853 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070853) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_070853
    g32p_supplierForest_actual_136596

def g32p_supplierForest_node_070860 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070860 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070860 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_052114 := by
  decide +kernel

theorem g32p_supplierForest_actual_070860 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070860) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_070860
    g32p_supplierForest_actual_052114

def g32p_supplierForest_node_070971 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_070971 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070971 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_063947 := by
  decide +kernel

theorem g32p_supplierForest_actual_070971 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070971) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_070971
    g32p_supplierForest_actual_063947

def g32p_supplierForest_node_070985 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_070985 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070985 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_136517 := by
  decide +kernel

theorem g32p_supplierForest_actual_070985 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070985) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_070985
    g32p_supplierForest_actual_136517

def g32p_supplierForest_node_071002 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071002 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071002 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057799 := by
  decide +kernel

theorem g32p_supplierForest_actual_071002 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071002) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_071002
    g32p_supplierForest_actual_057799

def g32p_supplierForest_node_071008 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071008 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071008 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057823 := by
  decide +kernel

theorem g32p_supplierForest_actual_071008 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071008) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_071008
    g32p_supplierForest_actual_057823

def g32p_supplierForest_node_071081 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_071081 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071081 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_058752 := by
  decide +kernel

theorem g32p_supplierForest_actual_071081 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071081) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_071081
    g32p_supplierForest_actual_058752

def g32p_supplierForest_node_071087 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_071087 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071087 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_130742 := by
  decide +kernel

theorem g32p_supplierForest_actual_071087 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071087) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_071087
    g32p_supplierForest_actual_130742

def g32p_supplierForest_node_071119 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_071119 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071119 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_136375 := by
  decide +kernel

theorem g32p_supplierForest_actual_071119 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071119) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_071119
    g32p_supplierForest_actual_136375

def g32p_supplierForest_node_071142 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_071142 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071142 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010641 := by
  decide +kernel

theorem g32p_supplierForest_actual_071142 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071142) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_071142
    g32p_supplierForest_actual_010641

def g32p_supplierForest_node_071184 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_071184 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071184 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_136639 := by
  decide +kernel

theorem g32p_supplierForest_actual_071184 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071184) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_071184
    g32p_supplierForest_actual_136639

def g32p_supplierForest_node_071186 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071186 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071186 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_136816 := by
  decide +kernel

theorem g32p_supplierForest_actual_071186 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071186) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 0 g32p_supplierForest_edge_071186
    g32p_supplierForest_actual_136816

def g32p_supplierForest_node_071256 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_071256 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071256 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_136855 := by
  decide +kernel

theorem g32p_supplierForest_actual_071256 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071256) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_071256
    g32p_supplierForest_actual_136855

def g32p_supplierForest_node_071294 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_071294 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071294 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_057027 := by
  decide +kernel

theorem g32p_supplierForest_actual_071294 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071294) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_071294
    g32p_supplierForest_actual_057027

def g32p_supplierForest_node_071353 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071353 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071353 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_139332 := by
  decide +kernel

theorem g32p_supplierForest_actual_071353 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071353) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_071353
    g32p_supplierForest_actual_139332

def g32p_supplierForest_node_071366 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_071366 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071366 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011180 := by
  decide +kernel

theorem g32p_supplierForest_actual_071366 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071366) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_071366
    g32p_supplierForest_actual_011180

def g32p_supplierForest_node_071405 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_071405 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071405 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011250 := by
  decide +kernel

theorem g32p_supplierForest_actual_071405 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071405) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_071405
    g32p_supplierForest_actual_011250

def g32p_supplierForest_node_071540 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_071540 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071540 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_070813 := by
  decide +kernel

theorem g32p_supplierForest_actual_071540 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071540) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_071540
    g32p_supplierForest_actual_070813

def g32p_supplierForest_node_071621 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_071621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071621 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_055765 := by
  decide +kernel

theorem g32p_supplierForest_actual_071621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071621) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_071621
    g32p_supplierForest_actual_055765

def g32p_supplierForest_node_071788 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071788 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071788 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_151501 := by
  decide +kernel

theorem g32p_supplierForest_actual_071788 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071788) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_071788
    g32p_supplierForest_actual_151501

def g32p_supplierForest_node_071871 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_071871 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071871 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014294 := by
  decide +kernel

theorem g32p_supplierForest_actual_071871 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071871) ∧
        IsConj g (g32p_literalRepresentative 48) := by
  exact g32p_archive_step_lift _ _ 48 0 g32p_supplierForest_edge_071871
    g32p_supplierForest_actual_014294

def g32p_supplierForest_node_071891 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071891 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071891 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_147998 := by
  decide +kernel

theorem g32p_supplierForest_actual_071891 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071891) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_071891
    g32p_supplierForest_actual_147998

def g32p_supplierForest_node_071916 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_071916 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071916 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087012 := by
  decide +kernel

theorem g32p_supplierForest_actual_071916 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071916) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_071916
    g32p_supplierForest_actual_087012

def g32p_supplierForest_node_071961 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071961 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071961 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072478 := by
  decide +kernel

theorem g32p_supplierForest_actual_071961 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071961) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_071961
    g32p_supplierForest_actual_072478

def g32p_supplierForest_node_072077 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_072077 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072077 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077678 := by
  decide +kernel

theorem g32p_supplierForest_actual_072077 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072077) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_072077
    g32p_supplierForest_actual_077678

def g32p_supplierForest_node_072099 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072099 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072099 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_101784 := by
  decide +kernel

theorem g32p_supplierForest_actual_072099 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072099) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_072099
    g32p_supplierForest_actual_101784

def g32p_supplierForest_node_072114 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_072114 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072114 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072597 := by
  decide +kernel

theorem g32p_supplierForest_actual_072114 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072114) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_072114
    g32p_supplierForest_actual_072597

def g32p_supplierForest_node_072182 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_072182 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072182 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015671 := by
  decide +kernel

theorem g32p_supplierForest_actual_072182 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072182) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072182
    g32p_supplierForest_actual_015671

def g32p_supplierForest_node_072215 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_072215 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072215 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082075 := by
  decide +kernel

theorem g32p_supplierForest_actual_072215 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072215) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072215
    g32p_supplierForest_actual_082075

def g32p_supplierForest_node_072301 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_072301 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072301 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082201 := by
  decide +kernel

theorem g32p_supplierForest_actual_072301 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072301) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072301
    g32p_supplierForest_actual_082201

def g32p_supplierForest_node_072316 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072316 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072316 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014907 := by
  decide +kernel

theorem g32p_supplierForest_actual_072316 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072316) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_072316
    g32p_supplierForest_actual_014907

def g32p_supplierForest_node_072338 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072338 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082241 := by
  decide +kernel

theorem g32p_supplierForest_actual_072338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072338) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072338
    g32p_supplierForest_actual_082241

def g32p_supplierForest_node_072360 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072360 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_084309 := by
  decide +kernel

theorem g32p_supplierForest_actual_072360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072360) ∧
        IsConj g (g32p_literalRepresentative 80) := by
  exact g32p_archive_step_lift _ _ 80 1 g32p_supplierForest_edge_072360
    g32p_supplierForest_actual_084309

def g32p_supplierForest_node_072370 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_072370 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072370 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_149124 := by
  decide +kernel

theorem g32p_supplierForest_actual_072370 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072370) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_072370
    g32p_supplierForest_actual_149124

def g32p_supplierForest_node_072408 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072408 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072408 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099393 := by
  decide +kernel

theorem g32p_supplierForest_actual_072408 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072408) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_072408
    g32p_supplierForest_actual_099393

def g32p_supplierForest_node_072469 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_072469 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072469 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073319 := by
  decide +kernel

theorem g32p_supplierForest_actual_072469 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072469) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_072469
    g32p_supplierForest_actual_073319

def g32p_supplierForest_node_072481 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072481 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072481 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092229 := by
  decide +kernel

theorem g32p_supplierForest_actual_072481 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072481) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_072481
    g32p_supplierForest_actual_092229

def g32p_supplierForest_node_072504 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_072504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072504 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_023528 := by
  decide +kernel

theorem g32p_supplierForest_actual_072504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072504) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_072504
    g32p_supplierForest_actual_023528

def g32p_supplierForest_node_072509 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072509 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072509 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_092456 := by
  decide +kernel

theorem g32p_supplierForest_actual_072509 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072509) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_072509
    g32p_supplierForest_actual_092456

def g32p_supplierForest_node_072633 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072633 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072633 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094861 := by
  decide +kernel

theorem g32p_supplierForest_actual_072633 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072633) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_072633
    g32p_supplierForest_actual_094861

def g32p_supplierForest_node_072732 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_072732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072732 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_021240 := by
  decide +kernel

theorem g32p_supplierForest_actual_072732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072732) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_072732
    g32p_supplierForest_actual_021240

def g32p_supplierForest_node_072817 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072817 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072817 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082856 := by
  decide +kernel

theorem g32p_supplierForest_actual_072817 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072817) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072817
    g32p_supplierForest_actual_082856

def g32p_supplierForest_node_072841 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072841 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072852 := by
  decide +kernel

theorem g32p_supplierForest_actual_072841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072841) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_072841
    g32p_supplierForest_actual_072852

def g32p_supplierForest_node_072893 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_072893 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072893 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_084683 := by
  decide +kernel

theorem g32p_supplierForest_actual_072893 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072893) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 1 g32p_supplierForest_edge_072893
    g32p_supplierForest_actual_084683

def g32p_supplierForest_node_072950 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_072950 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072950 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013596 := by
  decide +kernel

theorem g32p_supplierForest_actual_072950 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072950) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 3 g32p_supplierForest_edge_072950
    g32p_supplierForest_actual_013596

def g32p_supplierForest_node_072964 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_072964 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072964 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072674 := by
  decide +kernel

theorem g32p_supplierForest_actual_072964 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072964) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_072964
    g32p_supplierForest_actual_072674

def g32p_supplierForest_node_073118 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073118 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073118 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073165 := by
  decide +kernel

theorem g32p_supplierForest_actual_073118 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073118) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_073118
    g32p_supplierForest_actual_073165

def g32p_supplierForest_node_073147 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073147 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073147 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080599 := by
  decide +kernel

theorem g32p_supplierForest_actual_073147 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073147) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_073147
    g32p_supplierForest_actual_080599

def g32p_supplierForest_node_073171 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_073171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073171 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076485 := by
  decide +kernel

theorem g32p_supplierForest_actual_073171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073171) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_073171
    g32p_supplierForest_actual_076485

def g32p_supplierForest_node_073234 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_073234 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073234 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_017178 := by
  decide +kernel

theorem g32p_supplierForest_actual_073234 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073234) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_073234
    g32p_supplierForest_actual_017178

def g32p_supplierForest_node_073332 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_073332 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073332 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012580 := by
  decide +kernel

theorem g32p_supplierForest_actual_073332 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073332) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_073332
    g32p_supplierForest_actual_012580

def g32p_supplierForest_node_073349 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073349 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073349 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074515 := by
  decide +kernel

theorem g32p_supplierForest_actual_073349 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073349) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_073349
    g32p_supplierForest_actual_074515

def g32p_supplierForest_node_073512 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073512 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073512 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086461 := by
  decide +kernel

theorem g32p_supplierForest_actual_073512 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073512) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_073512
    g32p_supplierForest_actual_086461

def g32p_supplierForest_node_073571 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_073571 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073571 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_085823 := by
  decide +kernel

theorem g32p_supplierForest_actual_073571 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073571) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_073571
    g32p_supplierForest_actual_085823

def g32p_supplierForest_node_073584 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_073584 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073584 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083832 := by
  decide +kernel

theorem g32p_supplierForest_actual_073584 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073584) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 0 g32p_supplierForest_edge_073584
    g32p_supplierForest_actual_083832

def g32p_supplierForest_node_073734 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073734 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073734 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072565 := by
  decide +kernel

theorem g32p_supplierForest_actual_073734 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073734) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_073734
    g32p_supplierForest_actual_072565

def g32p_supplierForest_node_073813 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073813 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073813 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_148478 := by
  decide +kernel

theorem g32p_supplierForest_actual_073813 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073813) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_073813
    g32p_supplierForest_actual_148478

def g32p_supplierForest_node_073824 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073824 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_014944 := by
  decide +kernel

theorem g32p_supplierForest_actual_073824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073824) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_073824
    g32p_supplierForest_actual_014944

def g32p_supplierForest_node_073932 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073932 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073932 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024168 := by
  decide +kernel

theorem g32p_supplierForest_actual_073932 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073932) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_073932
    g32p_supplierForest_actual_024168

def g32p_supplierForest_node_073990 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073990 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073990 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015081 := by
  decide +kernel

theorem g32p_supplierForest_actual_073990 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073990) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_073990
    g32p_supplierForest_actual_015081

def g32p_supplierForest_node_074328 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074328 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074328 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_090547 := by
  decide +kernel

theorem g32p_supplierForest_actual_074328 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074328) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_074328
    g32p_supplierForest_actual_090547

def g32p_supplierForest_node_074357 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074357 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074357 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073614 := by
  decide +kernel

theorem g32p_supplierForest_actual_074357 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074357) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 1 g32p_supplierForest_edge_074357
    g32p_supplierForest_actual_073614

def g32p_supplierForest_node_074368 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_074368 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074368 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082261 := by
  decide +kernel

theorem g32p_supplierForest_actual_074368 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074368) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_074368
    g32p_supplierForest_actual_082261

def g32p_supplierForest_node_074422 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_074422 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074422 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_085070 := by
  decide +kernel

theorem g32p_supplierForest_actual_074422 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074422) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_074422
    g32p_supplierForest_actual_085070

def g32p_supplierForest_node_074454 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_074454 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074454 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_020526 := by
  decide +kernel

theorem g32p_supplierForest_actual_074454 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074454) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_074454
    g32p_supplierForest_actual_020526

def g32p_supplierForest_node_074514 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074514 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074514 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_017738 := by
  decide +kernel

theorem g32p_supplierForest_actual_074514 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074514) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_074514
    g32p_supplierForest_actual_017738

def g32p_supplierForest_node_074561 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074561 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074561 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_088009 := by
  decide +kernel

theorem g32p_supplierForest_actual_074561 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074561) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_074561
    g32p_supplierForest_actual_088009

def g32p_supplierForest_node_074591 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_074591 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074591 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074494 := by
  decide +kernel

theorem g32p_supplierForest_actual_074591 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074591) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_074591
    g32p_supplierForest_actual_074494

def g32p_supplierForest_node_074628 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074628 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074628 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_095344 := by
  decide +kernel

theorem g32p_supplierForest_actual_074628 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074628) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_074628
    g32p_supplierForest_actual_095344

def g32p_supplierForest_node_074722 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_074722 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074722 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075095 := by
  decide +kernel

theorem g32p_supplierForest_actual_074722 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074722) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_074722
    g32p_supplierForest_actual_075095

def g32p_supplierForest_node_074767 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_074767 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074767 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097384 := by
  decide +kernel

theorem g32p_supplierForest_actual_074767 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074767) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_074767
    g32p_supplierForest_actual_097384

def g32p_supplierForest_node_074841 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_074841 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074841 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088738 := by
  decide +kernel

theorem g32p_supplierForest_actual_074841 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074841) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_074841
    g32p_supplierForest_actual_088738

def g32p_supplierForest_node_074874 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074874 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074874 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097628 := by
  decide +kernel

theorem g32p_supplierForest_actual_074874 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074874) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_074874
    g32p_supplierForest_actual_097628

def g32p_supplierForest_node_074877 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074877 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074877 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097572 := by
  decide +kernel

theorem g32p_supplierForest_actual_074877 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074877) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_074877
    g32p_supplierForest_actual_097572

def g32p_supplierForest_node_074883 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_074883 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074883 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085355 := by
  decide +kernel

theorem g32p_supplierForest_actual_074883 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074883) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_074883
    g32p_supplierForest_actual_085355

def g32p_supplierForest_node_074948 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_074948 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074948 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080367 := by
  decide +kernel

theorem g32p_supplierForest_actual_074948 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074948) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_074948
    g32p_supplierForest_actual_080367

def g32p_supplierForest_node_074970 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_074970 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074970 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088732 := by
  decide +kernel

theorem g32p_supplierForest_actual_074970 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074970) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_074970
    g32p_supplierForest_actual_088732

def g32p_supplierForest_node_074982 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_074982 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074982 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_013866 := by
  decide +kernel

theorem g32p_supplierForest_actual_074982 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074982) ∧
        IsConj g (g32p_literalRepresentative 10) := by
  exact g32p_archive_step_lift _ _ 10 2 g32p_supplierForest_edge_074982
    g32p_supplierForest_actual_013866

def g32p_supplierForest_node_075057 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075057 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086813 := by
  decide +kernel

theorem g32p_supplierForest_actual_075057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075057) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_075057
    g32p_supplierForest_actual_086813

def g32p_supplierForest_node_075075 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075075 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075075 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085605 := by
  decide +kernel

theorem g32p_supplierForest_actual_075075 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075075) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_075075
    g32p_supplierForest_actual_085605

def g32p_supplierForest_node_075084 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075084 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075084 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088711 := by
  decide +kernel

theorem g32p_supplierForest_actual_075084 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075084) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_075084
    g32p_supplierForest_actual_088711

def g32p_supplierForest_node_075178 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_075178 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075178 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085730 := by
  decide +kernel

theorem g32p_supplierForest_actual_075178 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075178) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_075178
    g32p_supplierForest_actual_085730

def g32p_supplierForest_node_075197 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_075197 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075197 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077169 := by
  decide +kernel

theorem g32p_supplierForest_actual_075197 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075197) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_075197
    g32p_supplierForest_actual_077169

def g32p_supplierForest_node_075229 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075229 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075229 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076132 := by
  decide +kernel

theorem g32p_supplierForest_actual_075229 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075229) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_075229
    g32p_supplierForest_actual_076132

def g32p_supplierForest_node_075279 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075279 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075279 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_072170 := by
  decide +kernel

theorem g32p_supplierForest_actual_075279 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075279) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 1 g32p_supplierForest_edge_075279
    g32p_supplierForest_actual_072170

def g32p_supplierForest_node_075411 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075411 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075411 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075413 := by
  decide +kernel

theorem g32p_supplierForest_actual_075411 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075411) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_075411
    g32p_supplierForest_actual_075413

def g32p_supplierForest_node_075416 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_075416 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075416 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075499 := by
  decide +kernel

theorem g32p_supplierForest_actual_075416 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075416) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_075416
    g32p_supplierForest_actual_075499

def g32p_supplierForest_node_075471 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075471 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075471 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_090445 := by
  decide +kernel

theorem g32p_supplierForest_actual_075471 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075471) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_075471
    g32p_supplierForest_actual_090445

def g32p_supplierForest_node_075508 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_075508 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075508 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072298 := by
  decide +kernel

theorem g32p_supplierForest_actual_075508 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075508) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_075508
    g32p_supplierForest_actual_072298

def g32p_supplierForest_node_075539 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075539 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098822 := by
  decide +kernel

theorem g32p_supplierForest_actual_075539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075539) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_075539
    g32p_supplierForest_actual_098822

def g32p_supplierForest_node_075701 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075701 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075701 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076365 := by
  decide +kernel

theorem g32p_supplierForest_actual_075701 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075701) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_075701
    g32p_supplierForest_actual_076365

def g32p_supplierForest_node_075710 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075710 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075710 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_023234 := by
  decide +kernel

theorem g32p_supplierForest_actual_075710 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075710) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_075710
    g32p_supplierForest_actual_023234

def g32p_supplierForest_node_075745 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_075745 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075745 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078146 := by
  decide +kernel

theorem g32p_supplierForest_actual_075745 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075745) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_075745
    g32p_supplierForest_actual_078146

def g32p_supplierForest_node_075758 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075758 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075758 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081570 := by
  decide +kernel

theorem g32p_supplierForest_actual_075758 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075758) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 0 g32p_supplierForest_edge_075758
    g32p_supplierForest_actual_081570

def g32p_supplierForest_node_075844 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_075844 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075844 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_022492 := by
  decide +kernel

theorem g32p_supplierForest_actual_075844 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075844) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_075844
    g32p_supplierForest_actual_022492

def g32p_supplierForest_node_076023 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076023 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076023 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_086993 := by
  decide +kernel

theorem g32p_supplierForest_actual_076023 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076023) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_076023
    g32p_supplierForest_actual_086993

def g32p_supplierForest_node_076034 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076034 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076034 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085048 := by
  decide +kernel

theorem g32p_supplierForest_actual_076034 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076034) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_076034
    g32p_supplierForest_actual_085048

def g32p_supplierForest_node_076039 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_076039 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076039 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_086705 := by
  decide +kernel

theorem g32p_supplierForest_actual_076039 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076039) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_076039
    g32p_supplierForest_actual_086705

def g32p_supplierForest_node_076040 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_076040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076040 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082277 := by
  decide +kernel

theorem g32p_supplierForest_actual_076040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076040) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_076040
    g32p_supplierForest_actual_082277

def g32p_supplierForest_node_076044 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_076044 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076044 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_081091 := by
  decide +kernel

theorem g32p_supplierForest_actual_076044 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076044) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_076044
    g32p_supplierForest_actual_081091

def g32p_supplierForest_node_076051 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076051 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076051 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_086718 := by
  decide +kernel

theorem g32p_supplierForest_actual_076051 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076051) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 0 g32p_supplierForest_edge_076051
    g32p_supplierForest_actual_086718

def g32p_supplierForest_node_076052 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076052 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076052 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075479 := by
  decide +kernel

theorem g32p_supplierForest_actual_076052 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076052) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_076052
    g32p_supplierForest_actual_075479

def g32p_supplierForest_node_076164 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_076164 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076164 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_090838 := by
  decide +kernel

theorem g32p_supplierForest_actual_076164 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076164) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_076164
    g32p_supplierForest_actual_090838

def g32p_supplierForest_node_076233 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_076233 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076233 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018522 := by
  decide +kernel

theorem g32p_supplierForest_actual_076233 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076233) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_076233
    g32p_supplierForest_actual_018522

def g32p_supplierForest_node_076275 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076275 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076275 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077677 := by
  decide +kernel

theorem g32p_supplierForest_actual_076275 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076275) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_076275
    g32p_supplierForest_actual_077677

def g32p_supplierForest_node_076284 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076284 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076284 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_018719 := by
  decide +kernel

theorem g32p_supplierForest_actual_076284 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076284) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_076284
    g32p_supplierForest_actual_018719

def g32p_supplierForest_node_076357 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_076357 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076357 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077312 := by
  decide +kernel

theorem g32p_supplierForest_actual_076357 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076357) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_076357
    g32p_supplierForest_actual_077312

def g32p_supplierForest_node_076412 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_076412 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076412 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076410 := by
  decide +kernel

theorem g32p_supplierForest_actual_076412 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076412) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_076412
    g32p_supplierForest_actual_076410

def g32p_supplierForest_node_076414 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076414 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076414 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077227 := by
  decide +kernel

theorem g32p_supplierForest_actual_076414 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076414) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_076414
    g32p_supplierForest_actual_077227

def g32p_supplierForest_node_076435 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_076435 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076435 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087165 := by
  decide +kernel

theorem g32p_supplierForest_actual_076435 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076435) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 0 g32p_supplierForest_edge_076435
    g32p_supplierForest_actual_087165

def g32p_supplierForest_node_076514 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_076514 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076514 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_088104 := by
  decide +kernel

theorem g32p_supplierForest_actual_076514 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076514) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_076514
    g32p_supplierForest_actual_088104

def g32p_supplierForest_node_076529 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076529 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075764 := by
  decide +kernel

theorem g32p_supplierForest_actual_076529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076529) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 1 g32p_supplierForest_edge_076529
    g32p_supplierForest_actual_075764

def g32p_supplierForest_node_076537 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_076537 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076537 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_087280 := by
  decide +kernel

theorem g32p_supplierForest_actual_076537 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076537) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_076537
    g32p_supplierForest_actual_087280

def g32p_supplierForest_node_076617 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076617 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076617 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_075762 := by
  decide +kernel

theorem g32p_supplierForest_actual_076617 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076617) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_076617
    g32p_supplierForest_actual_075762

def g32p_supplierForest_node_076696 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_076696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076696 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093424 := by
  decide +kernel

theorem g32p_supplierForest_actual_076696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076696) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_076696
    g32p_supplierForest_actual_093424

def g32p_supplierForest_node_076756 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_076756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076756 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_145252 := by
  decide +kernel

theorem g32p_supplierForest_actual_076756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076756) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_076756
    g32p_supplierForest_actual_145252

def g32p_supplierForest_node_076825 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_076825 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076825 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_088661 := by
  decide +kernel

theorem g32p_supplierForest_actual_076825 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076825) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_076825
    g32p_supplierForest_actual_088661

def g32p_supplierForest_node_076833 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_076833 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076833 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_014585 := by
  decide +kernel

theorem g32p_supplierForest_actual_076833 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076833) ∧
        IsConj g (g32p_literalRepresentative 12) := by
  exact g32p_archive_step_lift _ _ 12 3 g32p_supplierForest_edge_076833
    g32p_supplierForest_actual_014585

def g32p_supplierForest_node_076966 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_076966 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076966 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_080148 := by
  decide +kernel

theorem g32p_supplierForest_actual_076966 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076966) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_076966
    g32p_supplierForest_actual_080148

def g32p_supplierForest_node_077189 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077189 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077189 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_020353 := by
  decide +kernel

theorem g32p_supplierForest_actual_077189 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077189) ∧
        IsConj g (g32p_literalRepresentative 27) := by
  exact g32p_archive_step_lift _ _ 27 0 g32p_supplierForest_edge_077189
    g32p_supplierForest_actual_020353

def g32p_supplierForest_node_077258 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_077258 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077258 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_082733 := by
  decide +kernel

theorem g32p_supplierForest_actual_077258 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077258) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_077258
    g32p_supplierForest_actual_082733

def g32p_supplierForest_node_077366 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077366 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077366 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088293 := by
  decide +kernel

theorem g32p_supplierForest_actual_077366 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077366) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_077366
    g32p_supplierForest_actual_088293

def g32p_supplierForest_node_077435 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077435 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077435 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077425 := by
  decide +kernel

theorem g32p_supplierForest_actual_077435 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077435) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_077435
    g32p_supplierForest_actual_077425

def g32p_supplierForest_node_077436 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077436 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077436 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088383 := by
  decide +kernel

theorem g32p_supplierForest_actual_077436 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077436) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_077436
    g32p_supplierForest_actual_088383

def g32p_supplierForest_node_077510 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_077510 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077510 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012566 := by
  decide +kernel

theorem g32p_supplierForest_actual_077510 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077510) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_077510
    g32p_supplierForest_actual_012566

def g32p_supplierForest_node_077515 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077515 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077515 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077546 := by
  decide +kernel

theorem g32p_supplierForest_actual_077515 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077515) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_077515
    g32p_supplierForest_actual_077546

def g32p_supplierForest_node_077557 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077557 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077557 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_089585 := by
  decide +kernel

theorem g32p_supplierForest_actual_077557 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077557) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_077557
    g32p_supplierForest_actual_089585

def g32p_supplierForest_node_077634 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_077634 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077634 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073511 := by
  decide +kernel

theorem g32p_supplierForest_actual_077634 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077634) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_077634
    g32p_supplierForest_actual_073511

def g32p_supplierForest_node_077662 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_077662 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077662 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_083491 := by
  decide +kernel

theorem g32p_supplierForest_actual_077662 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077662) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_077662
    g32p_supplierForest_actual_083491

def g32p_supplierForest_node_077668 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077668 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077668 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_073853 := by
  decide +kernel

theorem g32p_supplierForest_actual_077668 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077668) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_077668
    g32p_supplierForest_actual_073853

def g32p_supplierForest_node_077676 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077676 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077676 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077677 := by
  decide +kernel

theorem g32p_supplierForest_actual_077676 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077676) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_077676
    g32p_supplierForest_actual_077677

def g32p_supplierForest_node_077696 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077696 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073709 := by
  decide +kernel

theorem g32p_supplierForest_actual_077696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077696) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_077696
    g32p_supplierForest_actual_073709

def g32p_supplierForest_node_077767 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077767 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077767 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_016458 := by
  decide +kernel

theorem g32p_supplierForest_actual_077767 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077767) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_077767
    g32p_supplierForest_actual_016458

def g32p_supplierForest_node_077850 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_077850 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077850 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_013334 := by
  decide +kernel

theorem g32p_supplierForest_actual_077850 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077850) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_077850
    g32p_supplierForest_actual_013334

def g32p_supplierForest_node_077876 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_077876 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077876 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_077873 := by
  decide +kernel

theorem g32p_supplierForest_actual_077876 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077876) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_077876
    g32p_supplierForest_actual_077873

def g32p_supplierForest_node_077900 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077900 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077900 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_074661 := by
  decide +kernel

theorem g32p_supplierForest_actual_077900 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077900) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_077900
    g32p_supplierForest_actual_074661

def g32p_supplierForest_node_077951 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_077951 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077951 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_017862 := by
  decide +kernel

theorem g32p_supplierForest_actual_077951 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077951) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_077951
    g32p_supplierForest_actual_017862

def g32p_supplierForest_node_077983 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077983 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077983 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_144894 := by
  decide +kernel

theorem g32p_supplierForest_actual_077983 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077983) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_077983
    g32p_supplierForest_actual_144894

end HodgeLean.Foundations.Program

end
end
