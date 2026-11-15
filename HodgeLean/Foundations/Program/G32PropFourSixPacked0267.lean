import HodgeLean.Foundations.Program.G32PropFourSixPacked0263
import HodgeLean.Foundations.Program.G32PropFourSixPacked0264
import HodgeLean.Foundations.Program.G32PropFourSixPacked0265
import HodgeLean.Foundations.Program.G32PropFourSixPacked0266
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0242
import HodgeLean.Foundations.Program.G32PropFourSixPacked0243
import HodgeLean.Foundations.Program.G32PropFourSixPacked0244
import HodgeLean.Foundations.Program.G32PropFourSixPacked0251
import HodgeLean.Foundations.Program.G32PropFourSixPacked0252
import HodgeLean.Foundations.Program.G32PropFourSixPacked0253
import HodgeLean.Foundations.Program.G32PropFourSixPacked0254
import HodgeLean.Foundations.Program.G32PropFourSixPacked0256

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_096 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_066430 else g32p_supplierForest_node_066437) else (if i.val < 3 then g32p_supplierForest_node_066442 else g32p_supplierForest_node_066449)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_066478 else g32p_supplierForest_node_066548) else (if i.val < 7 then g32p_supplierForest_node_066556 else g32p_supplierForest_node_066557))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_066567 else g32p_supplierForest_node_066600) else (if i.val < 11 then g32p_supplierForest_node_066601 else g32p_supplierForest_node_066731)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_066732 else g32p_supplierForest_node_066734) else (if i.val < 15 then g32p_supplierForest_node_066753 else g32p_supplierForest_node_066766)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_066791 else g32p_supplierForest_node_066797) else (if i.val < 19 then g32p_supplierForest_node_066855 else g32p_supplierForest_node_066887)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_066888 else g32p_supplierForest_node_066900) else (if i.val < 23 then g32p_supplierForest_node_066933 else g32p_supplierForest_node_066934))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_066944 else g32p_supplierForest_node_066949) else (if i.val < 27 then g32p_supplierForest_node_066982 else g32p_supplierForest_node_066986)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_067014 else g32p_supplierForest_node_067018) else (if i.val < 31 then g32p_supplierForest_node_067022 else g32p_supplierForest_node_067060))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_067087 else g32p_supplierForest_node_067118) else (if i.val < 35 then g32p_supplierForest_node_067169 else g32p_supplierForest_node_067187)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_067193 else g32p_supplierForest_node_067194) else (if i.val < 39 then g32p_supplierForest_node_067224 else g32p_supplierForest_node_067267))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_067289 else g32p_supplierForest_node_067306) else (if i.val < 43 then g32p_supplierForest_node_067330 else g32p_supplierForest_node_067392)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_067408 else g32p_supplierForest_node_067422) else (if i.val < 47 then g32p_supplierForest_node_067442 else g32p_supplierForest_node_067509)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_067521 else g32p_supplierForest_node_067543) else (if i.val < 51 then g32p_supplierForest_node_067552 else g32p_supplierForest_node_067587)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_067632 else g32p_supplierForest_node_067757) else (if i.val < 55 then g32p_supplierForest_node_067765 else g32p_supplierForest_node_067786))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_067788 else g32p_supplierForest_node_067822) else (if i.val < 59 then g32p_supplierForest_node_067858 else g32p_supplierForest_node_067891)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_067905 else g32p_supplierForest_node_067911) else (if i.val < 63 then g32p_supplierForest_node_067936 else g32p_supplierForest_node_067957)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_067982 else g32p_supplierForest_node_067996) else (if i.val < 67 then g32p_supplierForest_node_068035 else g32p_supplierForest_node_068038)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_068072 else g32p_supplierForest_node_068087) else (if i.val < 71 then g32p_supplierForest_node_068114 else g32p_supplierForest_node_068146))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_068148 else g32p_supplierForest_node_068157) else (if i.val < 75 then g32p_supplierForest_node_068175 else g32p_supplierForest_node_068211)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_068226 else g32p_supplierForest_node_068232) else (if i.val < 79 then g32p_supplierForest_node_068233 else g32p_supplierForest_node_068244)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_068259 else g32p_supplierForest_node_068278) else (if i.val < 83 then g32p_supplierForest_node_068284 else g32p_supplierForest_node_068289)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_068291 else g32p_supplierForest_node_068310) else (if i.val < 87 then g32p_supplierForest_node_068365 else g32p_supplierForest_node_068455))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_068528 else g32p_supplierForest_node_068534) else (if i.val < 91 then g32p_supplierForest_node_068539 else g32p_supplierForest_node_068547)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_068565 else g32p_supplierForest_node_068576) else (if i.val < 95 then g32p_supplierForest_node_068581 else g32p_supplierForest_node_068594))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_068609 else g32p_supplierForest_node_068617) else (if i.val < 99 then g32p_supplierForest_node_068658 else g32p_supplierForest_node_068663)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_068665 else g32p_supplierForest_node_068670) else (if i.val < 103 then g32p_supplierForest_node_068694 else g32p_supplierForest_node_068726))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_068732 else g32p_supplierForest_node_068758) else (if i.val < 107 then g32p_supplierForest_node_068772 else g32p_supplierForest_node_068797)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_068814 else g32p_supplierForest_node_068821) else (if i.val < 111 then g32p_supplierForest_node_068829 else g32p_supplierForest_node_068832)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_068874 else g32p_supplierForest_node_068889) else (if i.val < 115 then g32p_supplierForest_node_068895 else g32p_supplierForest_node_068899)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_068905 else g32p_supplierForest_node_068918) else (if i.val < 119 then g32p_supplierForest_node_068949 else g32p_supplierForest_node_068976))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_069089 else g32p_supplierForest_node_069212) else (if i.val < 123 then g32p_supplierForest_node_069217 else g32p_supplierForest_node_069241)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_069248 else g32p_supplierForest_node_069275) else (if i.val < 127 then g32p_supplierForest_node_069302 else g32p_supplierForest_node_069309))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_069324 else g32p_supplierForest_node_069350) else (if i.val < 131 then g32p_supplierForest_node_069354 else g32p_supplierForest_node_069432)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_069479 else g32p_supplierForest_node_069482) else (if i.val < 135 then g32p_supplierForest_node_069529 else g32p_supplierForest_node_069537))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_069561 else g32p_supplierForest_node_069567) else (if i.val < 139 then g32p_supplierForest_node_069589 else g32p_supplierForest_node_069615)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_069632 else g32p_supplierForest_node_069647) else (if i.val < 143 then g32p_supplierForest_node_069685 else g32p_supplierForest_node_069699)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_069753 else g32p_supplierForest_node_069759) else (if i.val < 147 then g32p_supplierForest_node_069765 else g32p_supplierForest_node_069783)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_069788 else g32p_supplierForest_node_069799) else (if i.val < 151 then g32p_supplierForest_node_069826 else g32p_supplierForest_node_069842))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_069851 else g32p_supplierForest_node_069933) else (if i.val < 155 then g32p_supplierForest_node_069952 else g32p_supplierForest_node_069975)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_069990 else g32p_supplierForest_node_069996) else (if i.val < 159 then g32p_supplierForest_node_070026 else g32p_supplierForest_node_070043))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_070048 else g32p_supplierForest_node_070057) else (if i.val < 163 then g32p_supplierForest_node_070085 else g32p_supplierForest_node_070097)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_070101 else g32p_supplierForest_node_070109) else (if i.val < 167 then g32p_supplierForest_node_070112 else g32p_supplierForest_node_070154))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_070181 else g32p_supplierForest_node_070251) else (if i.val < 171 then g32p_supplierForest_node_070266 else g32p_supplierForest_node_070273)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_070286 else g32p_supplierForest_node_070297) else (if i.val < 175 then g32p_supplierForest_node_070307 else g32p_supplierForest_node_070328)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_070382 else g32p_supplierForest_node_070390) else (if i.val < 179 then g32p_supplierForest_node_070426 else g32p_supplierForest_node_070493)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_070502 else g32p_supplierForest_node_070571) else (if i.val < 183 then g32p_supplierForest_node_070580 else g32p_supplierForest_node_070586))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_070627 else g32p_supplierForest_node_070641) else (if i.val < 187 then g32p_supplierForest_node_070664 else g32p_supplierForest_node_070694)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_070748 else g32p_supplierForest_node_070753) else (if i.val < 191 then g32p_supplierForest_node_070761 else g32p_supplierForest_node_070786)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_070795 else g32p_supplierForest_node_070812) else (if i.val < 195 then g32p_supplierForest_node_070846 else g32p_supplierForest_node_070874)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_070924 else g32p_supplierForest_node_070957) else (if i.val < 199 then g32p_supplierForest_node_070976 else g32p_supplierForest_node_071022))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_071029 else g32p_supplierForest_node_071044) else (if i.val < 203 then g32p_supplierForest_node_071061 else g32p_supplierForest_node_071073)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_071100 else g32p_supplierForest_node_071104) else (if i.val < 207 then g32p_supplierForest_node_071118 else g32p_supplierForest_node_071129)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_071151 else g32p_supplierForest_node_071154) else (if i.val < 211 then g32p_supplierForest_node_071192 else g32p_supplierForest_node_071215)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_071249 else g32p_supplierForest_node_071264) else (if i.val < 215 then g32p_supplierForest_node_071302 else g32p_supplierForest_node_071310))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_071337 else g32p_supplierForest_node_071338) else (if i.val < 219 then g32p_supplierForest_node_071371 else g32p_supplierForest_node_071410)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_071477 else g32p_supplierForest_node_071478) else (if i.val < 223 then g32p_supplierForest_node_071505 else g32p_supplierForest_node_071514))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_071520 else g32p_supplierForest_node_071532) else (if i.val < 227 then g32p_supplierForest_node_071572 else g32p_supplierForest_node_071592)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_071627 else g32p_supplierForest_node_071693) else (if i.val < 231 then g32p_supplierForest_node_071730 else g32p_supplierForest_node_071789))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_071794 else g32p_supplierForest_node_071798) else (if i.val < 235 then g32p_supplierForest_node_071806 else g32p_supplierForest_node_071832)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_071860 else g32p_supplierForest_node_071892) else (if i.val < 239 then g32p_supplierForest_node_071940 else g32p_supplierForest_node_071960)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_071987 else g32p_supplierForest_node_072047) else (if i.val < 243 then g32p_supplierForest_node_072070 else g32p_supplierForest_node_072084)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_072132 else g32p_supplierForest_node_072164) else (if i.val < 247 then g32p_supplierForest_node_072171 else g32p_supplierForest_node_072173))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_072174 else g32p_supplierForest_node_072194) else (if i.val < 251 then g32p_supplierForest_node_072268 else g32p_supplierForest_node_072284)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_072325 else g32p_supplierForest_node_072337) else (if i.val < 255 then g32p_supplierForest_node_072349 else g32p_supplierForest_node_072379))))))))

def g32p_supplierForest_classes_096 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 38 else 38) else (if i.val < 3 then 43 else 38)) else (if i.val < 6 then (if i.val < 5 then 71 else 70) else (if i.val < 7 then 68 else 40))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 74 else 75) else (if i.val < 11 then 73 else 41)) else (if i.val < 14 then (if i.val < 13 then 21 else 21) else (if i.val < 15 then 40 else 20)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 73 else 73) else (if i.val < 19 then 75 else 38)) else (if i.val < 22 then (if i.val < 21 then 43 else 43) else (if i.val < 23 then 69 else 73))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 78 else 40) else (if i.val < 27 then 75 else 69)) else (if i.val < 30 then (if i.val < 29 then 43 else 41) else (if i.val < 31 then 75 else 70))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 71 else 21) else (if i.val < 35 then 21 else 73)) else (if i.val < 38 then (if i.val < 37 then 79 else 38) else (if i.val < 39 then 38 else 21))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 74 else 22) else (if i.val < 43 then 38 else 68)) else (if i.val < 46 then (if i.val < 45 then 73 else 22) else (if i.val < 47 then 21 else 21)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 42 else 41) else (if i.val < 51 then 43 else 40)) else (if i.val < 54 then (if i.val < 53 then 68 else 21) else (if i.val < 55 then 38 else 21))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 21 else 75) else (if i.val < 59 then 21 else 72)) else (if i.val < 62 then (if i.val < 61 then 39 else 73) else (if i.val < 63 then 38 else 70)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 39 else 74) else (if i.val < 67 then 38 else 71)) else (if i.val < 70 then (if i.val < 69 then 21 else 21) else (if i.val < 71 then 6 else 7))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 74 else 75) else (if i.val < 75 then 21 else 68)) else (if i.val < 78 then (if i.val < 77 then 21 else 21) else (if i.val < 79 then 41 else 38)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 39 else 41) else (if i.val < 83 then 70 else 71)) else (if i.val < 86 then (if i.val < 85 then 70 else 74) else (if i.val < 87 then 21 else 21))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 73 else 38) else (if i.val < 91 then 40 else 75)) else (if i.val < 94 then (if i.val < 93 then 21 else 22) else (if i.val < 95 then 73 else 73))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 21 else 73) else (if i.val < 99 then 19 else 42)) else (if i.val < 102 then (if i.val < 101 then 42 else 40) else (if i.val < 103 then 75 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 38 else 70) else (if i.val < 107 then 38 else 38)) else (if i.val < 110 then (if i.val < 109 then 73 else 73) else (if i.val < 111 then 21 else 38)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 71 else 38) else (if i.val < 115 then 7 else 38)) else (if i.val < 118 then (if i.val < 117 then 74 else 38) else (if i.val < 119 then 38 else 38))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 21 else 38) else (if i.val < 123 then 22 else 42)) else (if i.val < 126 then (if i.val < 125 then 75 else 38) else (if i.val < 127 then 41 else 21))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 20 else 21) else (if i.val < 131 then 38 else 74)) else (if i.val < 134 then (if i.val < 133 then 71 else 20) else (if i.val < 135 then 7 else 40))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 21 else 38) else (if i.val < 139 then 74 else 38)) else (if i.val < 142 then (if i.val < 141 then 43 else 41) else (if i.val < 143 then 20 else 38)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 21 else 74) else (if i.val < 147 then 73 else 43)) else (if i.val < 150 then (if i.val < 149 then 38 else 43) else (if i.val < 151 then 22 else 41))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 21 else 21) else (if i.val < 155 then 43 else 38)) else (if i.val < 158 then (if i.val < 157 then 38 else 74) else (if i.val < 159 then 38 else 41))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 38 else 38) else (if i.val < 163 then 68 else 38)) else (if i.val < 166 then (if i.val < 165 then 21 else 73) else (if i.val < 167 then 71 else 21))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 68 else 41) else (if i.val < 171 then 21 else 38)) else (if i.val < 174 then (if i.val < 173 then 6 else 21) else (if i.val < 175 then 39 else 38)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 74 else 72) else (if i.val < 179 then 73 else 73)) else (if i.val < 182 then (if i.val < 181 then 21 else 6) else (if i.val < 183 then 42 else 73))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 43 else 20) else (if i.val < 187 then 39 else 6)) else (if i.val < 190 then (if i.val < 189 then 21 else 21) else (if i.val < 191 then 38 else 72)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 38 else 7) else (if i.val < 195 then 75 else 21)) else (if i.val < 198 then (if i.val < 197 then 75 else 73) else (if i.val < 199 then 38 else 73))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 73 else 74) else (if i.val < 203 then 21 else 21)) else (if i.val < 206 then (if i.val < 205 then 21 else 43) else (if i.val < 207 then 43 else 72)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 41 else 41) else (if i.val < 211 then 74 else 68)) else (if i.val < 214 then (if i.val < 213 then 42 else 43) else (if i.val < 215 then 20 else 38))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 71 else 73) else (if i.val < 219 then 38 else 77)) else (if i.val < 222 then (if i.val < 221 then 72 else 21) else (if i.val < 223 then 38 else 38))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 38 else 22) else (if i.val < 227 then 23 else 73)) else (if i.val < 230 then (if i.val < 229 then 71 else 38) else (if i.val < 231 then 38 else 52))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 48 else 49) else (if i.val < 235 then 26 else 49)) else (if i.val < 238 then (if i.val < 237 then 49 else 80) else (if i.val < 239 then 56 else 46)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 48 else 48) else (if i.val < 243 then 49 else 49)) else (if i.val < 246 then (if i.val < 245 then 49 else 49) else (if i.val < 247 then 49 else 26))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 47 else 49) else (if i.val < 251 then 49 else 13)) else (if i.val < 254 then (if i.val < 253 then 25 else 9) else (if i.val < 255 then 49 else 49))))))))

theorem g32p_supplierForest_actual_096 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_096 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_096 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_066430
  · exact g32p_supplierForest_actual_066437
  · exact g32p_supplierForest_actual_066442
  · exact g32p_supplierForest_actual_066449
  · exact g32p_supplierForest_actual_066478
  · exact g32p_supplierForest_actual_066548
  · exact g32p_supplierForest_actual_066556
  · exact g32p_supplierForest_actual_066557
  · exact g32p_supplierForest_actual_066567
  · exact g32p_supplierForest_actual_066600
  · exact g32p_supplierForest_actual_066601
  · exact g32p_supplierForest_actual_066731
  · exact g32p_supplierForest_actual_066732
  · exact g32p_supplierForest_actual_066734
  · exact g32p_supplierForest_actual_066753
  · exact g32p_supplierForest_actual_066766
  · exact g32p_supplierForest_actual_066791
  · exact g32p_supplierForest_actual_066797
  · exact g32p_supplierForest_actual_066855
  · exact g32p_supplierForest_actual_066887
  · exact g32p_supplierForest_actual_066888
  · exact g32p_supplierForest_actual_066900
  · exact g32p_supplierForest_actual_066933
  · exact g32p_supplierForest_actual_066934
  · exact g32p_supplierForest_actual_066944
  · exact g32p_supplierForest_actual_066949
  · exact g32p_supplierForest_actual_066982
  · exact g32p_supplierForest_actual_066986
  · exact g32p_supplierForest_actual_067014
  · exact g32p_supplierForest_actual_067018
  · exact g32p_supplierForest_actual_067022
  · exact g32p_supplierForest_actual_067060
  · exact g32p_supplierForest_actual_067087
  · exact g32p_supplierForest_actual_067118
  · exact g32p_supplierForest_actual_067169
  · exact g32p_supplierForest_actual_067187
  · exact g32p_supplierForest_actual_067193
  · exact g32p_supplierForest_actual_067194
  · exact g32p_supplierForest_actual_067224
  · exact g32p_supplierForest_actual_067267
  · exact g32p_supplierForest_actual_067289
  · exact g32p_supplierForest_actual_067306
  · exact g32p_supplierForest_actual_067330
  · exact g32p_supplierForest_actual_067392
  · exact g32p_supplierForest_actual_067408
  · exact g32p_supplierForest_actual_067422
  · exact g32p_supplierForest_actual_067442
  · exact g32p_supplierForest_actual_067509
  · exact g32p_supplierForest_actual_067521
  · exact g32p_supplierForest_actual_067543
  · exact g32p_supplierForest_actual_067552
  · exact g32p_supplierForest_actual_067587
  · exact g32p_supplierForest_actual_067632
  · exact g32p_supplierForest_actual_067757
  · exact g32p_supplierForest_actual_067765
  · exact g32p_supplierForest_actual_067786
  · exact g32p_supplierForest_actual_067788
  · exact g32p_supplierForest_actual_067822
  · exact g32p_supplierForest_actual_067858
  · exact g32p_supplierForest_actual_067891
  · exact g32p_supplierForest_actual_067905
  · exact g32p_supplierForest_actual_067911
  · exact g32p_supplierForest_actual_067936
  · exact g32p_supplierForest_actual_067957
  · exact g32p_supplierForest_actual_067982
  · exact g32p_supplierForest_actual_067996
  · exact g32p_supplierForest_actual_068035
  · exact g32p_supplierForest_actual_068038
  · exact g32p_supplierForest_actual_068072
  · exact g32p_supplierForest_actual_068087
  · exact g32p_supplierForest_actual_068114
  · exact g32p_supplierForest_actual_068146
  · exact g32p_supplierForest_actual_068148
  · exact g32p_supplierForest_actual_068157
  · exact g32p_supplierForest_actual_068175
  · exact g32p_supplierForest_actual_068211
  · exact g32p_supplierForest_actual_068226
  · exact g32p_supplierForest_actual_068232
  · exact g32p_supplierForest_actual_068233
  · exact g32p_supplierForest_actual_068244
  · exact g32p_supplierForest_actual_068259
  · exact g32p_supplierForest_actual_068278
  · exact g32p_supplierForest_actual_068284
  · exact g32p_supplierForest_actual_068289
  · exact g32p_supplierForest_actual_068291
  · exact g32p_supplierForest_actual_068310
  · exact g32p_supplierForest_actual_068365
  · exact g32p_supplierForest_actual_068455
  · exact g32p_supplierForest_actual_068528
  · exact g32p_supplierForest_actual_068534
  · exact g32p_supplierForest_actual_068539
  · exact g32p_supplierForest_actual_068547
  · exact g32p_supplierForest_actual_068565
  · exact g32p_supplierForest_actual_068576
  · exact g32p_supplierForest_actual_068581
  · exact g32p_supplierForest_actual_068594
  · exact g32p_supplierForest_actual_068609
  · exact g32p_supplierForest_actual_068617
  · exact g32p_supplierForest_actual_068658
  · exact g32p_supplierForest_actual_068663
  · exact g32p_supplierForest_actual_068665
  · exact g32p_supplierForest_actual_068670
  · exact g32p_supplierForest_actual_068694
  · exact g32p_supplierForest_actual_068726
  · exact g32p_supplierForest_actual_068732
  · exact g32p_supplierForest_actual_068758
  · exact g32p_supplierForest_actual_068772
  · exact g32p_supplierForest_actual_068797
  · exact g32p_supplierForest_actual_068814
  · exact g32p_supplierForest_actual_068821
  · exact g32p_supplierForest_actual_068829
  · exact g32p_supplierForest_actual_068832
  · exact g32p_supplierForest_actual_068874
  · exact g32p_supplierForest_actual_068889
  · exact g32p_supplierForest_actual_068895
  · exact g32p_supplierForest_actual_068899
  · exact g32p_supplierForest_actual_068905
  · exact g32p_supplierForest_actual_068918
  · exact g32p_supplierForest_actual_068949
  · exact g32p_supplierForest_actual_068976
  · exact g32p_supplierForest_actual_069089
  · exact g32p_supplierForest_actual_069212
  · exact g32p_supplierForest_actual_069217
  · exact g32p_supplierForest_actual_069241
  · exact g32p_supplierForest_actual_069248
  · exact g32p_supplierForest_actual_069275
  · exact g32p_supplierForest_actual_069302
  · exact g32p_supplierForest_actual_069309
  · exact g32p_supplierForest_actual_069324
  · exact g32p_supplierForest_actual_069350
  · exact g32p_supplierForest_actual_069354
  · exact g32p_supplierForest_actual_069432
  · exact g32p_supplierForest_actual_069479
  · exact g32p_supplierForest_actual_069482
  · exact g32p_supplierForest_actual_069529
  · exact g32p_supplierForest_actual_069537
  · exact g32p_supplierForest_actual_069561
  · exact g32p_supplierForest_actual_069567
  · exact g32p_supplierForest_actual_069589
  · exact g32p_supplierForest_actual_069615
  · exact g32p_supplierForest_actual_069632
  · exact g32p_supplierForest_actual_069647
  · exact g32p_supplierForest_actual_069685
  · exact g32p_supplierForest_actual_069699
  · exact g32p_supplierForest_actual_069753
  · exact g32p_supplierForest_actual_069759
  · exact g32p_supplierForest_actual_069765
  · exact g32p_supplierForest_actual_069783
  · exact g32p_supplierForest_actual_069788
  · exact g32p_supplierForest_actual_069799
  · exact g32p_supplierForest_actual_069826
  · exact g32p_supplierForest_actual_069842
  · exact g32p_supplierForest_actual_069851
  · exact g32p_supplierForest_actual_069933
  · exact g32p_supplierForest_actual_069952
  · exact g32p_supplierForest_actual_069975
  · exact g32p_supplierForest_actual_069990
  · exact g32p_supplierForest_actual_069996
  · exact g32p_supplierForest_actual_070026
  · exact g32p_supplierForest_actual_070043
  · exact g32p_supplierForest_actual_070048
  · exact g32p_supplierForest_actual_070057
  · exact g32p_supplierForest_actual_070085
  · exact g32p_supplierForest_actual_070097
  · exact g32p_supplierForest_actual_070101
  · exact g32p_supplierForest_actual_070109
  · exact g32p_supplierForest_actual_070112
  · exact g32p_supplierForest_actual_070154
  · exact g32p_supplierForest_actual_070181
  · exact g32p_supplierForest_actual_070251
  · exact g32p_supplierForest_actual_070266
  · exact g32p_supplierForest_actual_070273
  · exact g32p_supplierForest_actual_070286
  · exact g32p_supplierForest_actual_070297
  · exact g32p_supplierForest_actual_070307
  · exact g32p_supplierForest_actual_070328
  · exact g32p_supplierForest_actual_070382
  · exact g32p_supplierForest_actual_070390
  · exact g32p_supplierForest_actual_070426
  · exact g32p_supplierForest_actual_070493
  · exact g32p_supplierForest_actual_070502
  · exact g32p_supplierForest_actual_070571
  · exact g32p_supplierForest_actual_070580
  · exact g32p_supplierForest_actual_070586
  · exact g32p_supplierForest_actual_070627
  · exact g32p_supplierForest_actual_070641
  · exact g32p_supplierForest_actual_070664
  · exact g32p_supplierForest_actual_070694
  · exact g32p_supplierForest_actual_070748
  · exact g32p_supplierForest_actual_070753
  · exact g32p_supplierForest_actual_070761
  · exact g32p_supplierForest_actual_070786
  · exact g32p_supplierForest_actual_070795
  · exact g32p_supplierForest_actual_070812
  · exact g32p_supplierForest_actual_070846
  · exact g32p_supplierForest_actual_070874
  · exact g32p_supplierForest_actual_070924
  · exact g32p_supplierForest_actual_070957
  · exact g32p_supplierForest_actual_070976
  · exact g32p_supplierForest_actual_071022
  · exact g32p_supplierForest_actual_071029
  · exact g32p_supplierForest_actual_071044
  · exact g32p_supplierForest_actual_071061
  · exact g32p_supplierForest_actual_071073
  · exact g32p_supplierForest_actual_071100
  · exact g32p_supplierForest_actual_071104
  · exact g32p_supplierForest_actual_071118
  · exact g32p_supplierForest_actual_071129
  · exact g32p_supplierForest_actual_071151
  · exact g32p_supplierForest_actual_071154
  · exact g32p_supplierForest_actual_071192
  · exact g32p_supplierForest_actual_071215
  · exact g32p_supplierForest_actual_071249
  · exact g32p_supplierForest_actual_071264
  · exact g32p_supplierForest_actual_071302
  · exact g32p_supplierForest_actual_071310
  · exact g32p_supplierForest_actual_071337
  · exact g32p_supplierForest_actual_071338
  · exact g32p_supplierForest_actual_071371
  · exact g32p_supplierForest_actual_071410
  · exact g32p_supplierForest_actual_071477
  · exact g32p_supplierForest_actual_071478
  · exact g32p_supplierForest_actual_071505
  · exact g32p_supplierForest_actual_071514
  · exact g32p_supplierForest_actual_071520
  · exact g32p_supplierForest_actual_071532
  · exact g32p_supplierForest_actual_071572
  · exact g32p_supplierForest_actual_071592
  · exact g32p_supplierForest_actual_071627
  · exact g32p_supplierForest_actual_071693
  · exact g32p_supplierForest_actual_071730
  · exact g32p_supplierForest_actual_071789
  · exact g32p_supplierForest_actual_071794
  · exact g32p_supplierForest_actual_071798
  · exact g32p_supplierForest_actual_071806
  · exact g32p_supplierForest_actual_071832
  · exact g32p_supplierForest_actual_071860
  · exact g32p_supplierForest_actual_071892
  · exact g32p_supplierForest_actual_071940
  · exact g32p_supplierForest_actual_071960
  · exact g32p_supplierForest_actual_071987
  · exact g32p_supplierForest_actual_072047
  · exact g32p_supplierForest_actual_072070
  · exact g32p_supplierForest_actual_072084
  · exact g32p_supplierForest_actual_072132
  · exact g32p_supplierForest_actual_072164
  · exact g32p_supplierForest_actual_072171
  · exact g32p_supplierForest_actual_072173
  · exact g32p_supplierForest_actual_072174
  · exact g32p_supplierForest_actual_072194
  · exact g32p_supplierForest_actual_072268
  · exact g32p_supplierForest_actual_072284
  · exact g32p_supplierForest_actual_072325
  · exact g32p_supplierForest_actual_072337
  · exact g32p_supplierForest_actual_072349
  · exact g32p_supplierForest_actual_072379

def g32p_supplierForest_nodes_097 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_072391 else g32p_supplierForest_node_072413) else (if i.val < 3 then g32p_supplierForest_node_072428 else g32p_supplierForest_node_072520)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_072534 else g32p_supplierForest_node_072535) else (if i.val < 7 then g32p_supplierForest_node_072543 else g32p_supplierForest_node_072547))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_072550 else g32p_supplierForest_node_072586) else (if i.val < 11 then g32p_supplierForest_node_072625 else g32p_supplierForest_node_072645)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_072651 else g32p_supplierForest_node_072700) else (if i.val < 15 then g32p_supplierForest_node_072743 else g32p_supplierForest_node_072806)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_072810 else g32p_supplierForest_node_072864) else (if i.val < 19 then g32p_supplierForest_node_072879 else g32p_supplierForest_node_072896)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_072906 else g32p_supplierForest_node_072939) else (if i.val < 23 then g32p_supplierForest_node_072944 else g32p_supplierForest_node_072956))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_072959 else g32p_supplierForest_node_072969) else (if i.val < 27 then g32p_supplierForest_node_072989 else g32p_supplierForest_node_072990)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_073046 else g32p_supplierForest_node_073060) else (if i.val < 31 then g32p_supplierForest_node_073072 else g32p_supplierForest_node_073084))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_073088 else g32p_supplierForest_node_073092) else (if i.val < 35 then g32p_supplierForest_node_073112 else g32p_supplierForest_node_073131)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_073133 else g32p_supplierForest_node_073150) else (if i.val < 39 then g32p_supplierForest_node_073204 else g32p_supplierForest_node_073218))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_073230 else g32p_supplierForest_node_073254) else (if i.val < 43 then g32p_supplierForest_node_073273 else g32p_supplierForest_node_073276)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_073288 else g32p_supplierForest_node_073307) else (if i.val < 47 then g32p_supplierForest_node_073310 else g32p_supplierForest_node_073396)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_073420 else g32p_supplierForest_node_073441) else (if i.val < 51 then g32p_supplierForest_node_073456 else g32p_supplierForest_node_073459)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_073472 else g32p_supplierForest_node_073503) else (if i.val < 55 then g32p_supplierForest_node_073506 else g32p_supplierForest_node_073521))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_073559 else g32p_supplierForest_node_073578) else (if i.val < 59 then g32p_supplierForest_node_073612 else g32p_supplierForest_node_073626)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_073676 else g32p_supplierForest_node_073690) else (if i.val < 63 then g32p_supplierForest_node_073700 else g32p_supplierForest_node_073720)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_073744 else g32p_supplierForest_node_073790) else (if i.val < 67 then g32p_supplierForest_node_073798 else g32p_supplierForest_node_073808)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_073851 else g32p_supplierForest_node_073871) else (if i.val < 71 then g32p_supplierForest_node_073912 else g32p_supplierForest_node_073960))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_073966 else g32p_supplierForest_node_073973) else (if i.val < 75 then g32p_supplierForest_node_073977 else g32p_supplierForest_node_073981)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_073982 else g32p_supplierForest_node_073996) else (if i.val < 79 then g32p_supplierForest_node_073999 else g32p_supplierForest_node_074015)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_074042 else g32p_supplierForest_node_074055) else (if i.val < 83 then g32p_supplierForest_node_074059 else g32p_supplierForest_node_074073)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_074080 else g32p_supplierForest_node_074128) else (if i.val < 87 then g32p_supplierForest_node_074130 else g32p_supplierForest_node_074138))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_074177 else g32p_supplierForest_node_074202) else (if i.val < 91 then g32p_supplierForest_node_074207 else g32p_supplierForest_node_074228)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_074236 else g32p_supplierForest_node_074251) else (if i.val < 95 then g32p_supplierForest_node_074300 else g32p_supplierForest_node_074314))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_074335 else g32p_supplierForest_node_074359) else (if i.val < 99 then g32p_supplierForest_node_074364 else g32p_supplierForest_node_074375)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_074379 else g32p_supplierForest_node_074410) else (if i.val < 103 then g32p_supplierForest_node_074473 else g32p_supplierForest_node_074507))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_074521 else g32p_supplierForest_node_074523) else (if i.val < 107 then g32p_supplierForest_node_074553 else g32p_supplierForest_node_074554)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_074577 else g32p_supplierForest_node_074581) else (if i.val < 111 then g32p_supplierForest_node_074616 else g32p_supplierForest_node_074622)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_074680 else g32p_supplierForest_node_074694) else (if i.val < 115 then g32p_supplierForest_node_074701 else g32p_supplierForest_node_074712)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_074745 else g32p_supplierForest_node_074773) else (if i.val < 119 then g32p_supplierForest_node_074796 else g32p_supplierForest_node_074806))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_074822 else g32p_supplierForest_node_074839) else (if i.val < 123 then g32p_supplierForest_node_074846 else g32p_supplierForest_node_074857)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_074862 else g32p_supplierForest_node_074880) else (if i.val < 127 then g32p_supplierForest_node_074909 else g32p_supplierForest_node_074918))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_074922 else g32p_supplierForest_node_074938) else (if i.val < 131 then g32p_supplierForest_node_074969 else g32p_supplierForest_node_075026)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_075032 else g32p_supplierForest_node_075082) else (if i.val < 135 then g32p_supplierForest_node_075093 else g32p_supplierForest_node_075094))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_075098 else g32p_supplierForest_node_075121) else (if i.val < 139 then g32p_supplierForest_node_075167 else g32p_supplierForest_node_075177)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_075199 else g32p_supplierForest_node_075201) else (if i.val < 143 then g32p_supplierForest_node_075213 else g32p_supplierForest_node_075220)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_075254 else g32p_supplierForest_node_075332) else (if i.val < 147 then g32p_supplierForest_node_075342 else g32p_supplierForest_node_075343)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_075353 else g32p_supplierForest_node_075379) else (if i.val < 151 then g32p_supplierForest_node_075387 else g32p_supplierForest_node_075399))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_075412 else g32p_supplierForest_node_075425) else (if i.val < 155 then g32p_supplierForest_node_075437 else g32p_supplierForest_node_075439)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_075461 else g32p_supplierForest_node_075553) else (if i.val < 159 then g32p_supplierForest_node_075558 else g32p_supplierForest_node_075571))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_075609 else g32p_supplierForest_node_075627) else (if i.val < 163 then g32p_supplierForest_node_075660 else g32p_supplierForest_node_075663)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_075702 else g32p_supplierForest_node_075708) else (if i.val < 167 then g32p_supplierForest_node_075721 else g32p_supplierForest_node_075725))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_075730 else g32p_supplierForest_node_075747) else (if i.val < 171 then g32p_supplierForest_node_075749 else g32p_supplierForest_node_075757)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_075790 else g32p_supplierForest_node_075830) else (if i.val < 175 then g32p_supplierForest_node_075843 else g32p_supplierForest_node_075856)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_075871 else g32p_supplierForest_node_075879) else (if i.val < 179 then g32p_supplierForest_node_075900 else g32p_supplierForest_node_075901)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_075915 else g32p_supplierForest_node_075922) else (if i.val < 183 then g32p_supplierForest_node_075934 else g32p_supplierForest_node_075950))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_075991 else g32p_supplierForest_node_075998) else (if i.val < 187 then g32p_supplierForest_node_076002 else g32p_supplierForest_node_076041)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_076057 else g32p_supplierForest_node_076075) else (if i.val < 191 then g32p_supplierForest_node_076116 else g32p_supplierForest_node_076136)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_076152 else g32p_supplierForest_node_076222) else (if i.val < 195 then g32p_supplierForest_node_076231 else g32p_supplierForest_node_076248)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_076253 else g32p_supplierForest_node_076387) else (if i.val < 199 then g32p_supplierForest_node_076409 else g32p_supplierForest_node_076417))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_076419 else g32p_supplierForest_node_076424) else (if i.val < 203 then g32p_supplierForest_node_076454 else g32p_supplierForest_node_076490)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_076524 else g32p_supplierForest_node_076536) else (if i.val < 207 then g32p_supplierForest_node_076549 else g32p_supplierForest_node_076575)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_076581 else g32p_supplierForest_node_076595) else (if i.val < 211 then g32p_supplierForest_node_076609 else g32p_supplierForest_node_076611)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_076708 else g32p_supplierForest_node_076724) else (if i.val < 215 then g32p_supplierForest_node_076733 else g32p_supplierForest_node_076742))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_076757 else g32p_supplierForest_node_076827) else (if i.val < 219 then g32p_supplierForest_node_076828 else g32p_supplierForest_node_076830)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_076874 else g32p_supplierForest_node_076876) else (if i.val < 223 then g32p_supplierForest_node_076885 else g32p_supplierForest_node_076888))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_076906 else g32p_supplierForest_node_076908) else (if i.val < 227 then g32p_supplierForest_node_076915 else g32p_supplierForest_node_076935)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_076941 else g32p_supplierForest_node_076947) else (if i.val < 231 then g32p_supplierForest_node_076949 else g32p_supplierForest_node_076951))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_076969 else g32p_supplierForest_node_076977) else (if i.val < 235 then g32p_supplierForest_node_076993 else g32p_supplierForest_node_077006)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_077008 else g32p_supplierForest_node_077057) else (if i.val < 239 then g32p_supplierForest_node_077139 else g32p_supplierForest_node_077141)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_077201 else g32p_supplierForest_node_077212) else (if i.val < 243 then g32p_supplierForest_node_077222 else g32p_supplierForest_node_077251)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_077255 else g32p_supplierForest_node_077288) else (if i.val < 247 then g32p_supplierForest_node_077428 else g32p_supplierForest_node_077446))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_077467 else g32p_supplierForest_node_077497) else (if i.val < 251 then g32p_supplierForest_node_077525 else g32p_supplierForest_node_077527)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_077532 else g32p_supplierForest_node_077559) else (if i.val < 255 then g32p_supplierForest_node_077561 else g32p_supplierForest_node_077569))))))))

def g32p_supplierForest_classes_097 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 49 else 47) else (if i.val < 3 then 25 else 50)) else (if i.val < 6 then (if i.val < 5 then 10 else 49) else (if i.val < 7 then 27 else 50))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 49) else (if i.val < 11 then 12 else 49)) else (if i.val < 14 then (if i.val < 13 then 49 else 49) else (if i.val < 15 then 26 else 49)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 12 else 85) else (if i.val < 19 then 49 else 46)) else (if i.val < 22 then (if i.val < 21 then 26 else 12) else (if i.val < 23 then 49 else 48))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 52) else (if i.val < 27 then 47 else 46)) else (if i.val < 30 then (if i.val < 29 then 48 else 46) else (if i.val < 31 then 49 else 49))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 49 else 48) else (if i.val < 35 then 9 else 27)) else (if i.val < 38 then (if i.val < 37 then 46 else 47) else (if i.val < 39 then 12 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 49 else 10) else (if i.val < 43 then 46 else 46)) else (if i.val < 46 then (if i.val < 45 then 46 else 47) else (if i.val < 47 then 46 else 26)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 27) else (if i.val < 51 then 84 else 26)) else (if i.val < 54 then (if i.val < 53 then 26 else 10) else (if i.val < 55 then 45 else 46))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 46 else 45) else (if i.val < 59 then 9 else 46)) else (if i.val < 62 then (if i.val < 61 then 9 else 84) else (if i.val < 63 then 26 else 9)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 46) else (if i.val < 67 then 46 else 54)) else (if i.val < 70 then (if i.val < 69 then 26 else 46) else (if i.val < 71 then 83 else 83))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 49 else 12) else (if i.val < 75 then 50 else 9)) else (if i.val < 78 then (if i.val < 77 then 46 else 49) else (if i.val < 79 then 46 else 26)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 9 else 83) else (if i.val < 83 then 46 else 46)) else (if i.val < 86 then (if i.val < 85 then 49 else 83) else (if i.val < 87 then 10 else 46))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 26 else 11) else (if i.val < 91 then 12 else 46)) else (if i.val < 94 then (if i.val < 93 then 46 else 49) else (if i.val < 95 then 27 else 49))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 47 else 49) else (if i.val < 99 then 49 else 49)) else (if i.val < 102 then (if i.val < 101 then 49 else 49) else (if i.val < 103 then 49 else 50))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 25 else 25) else (if i.val < 107 then 10 else 49)) else (if i.val < 110 then (if i.val < 109 then 27 else 45) else (if i.val < 111 then 12 else 46)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 47 else 54) else (if i.val < 115 then 46 else 27)) else (if i.val < 118 then (if i.val < 117 then 49 else 49) else (if i.val < 119 then 49 else 46))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 45 else 9) else (if i.val < 123 then 46 else 49)) else (if i.val < 126 then (if i.val < 125 then 48 else 80) else (if i.val < 127 then 12 else 25))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 47) else (if i.val < 131 then 46 else 48)) else (if i.val < 134 then (if i.val < 133 then 46 else 46) else (if i.val < 135 then 25 else 25))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 26 else 26) else (if i.val < 139 then 26 else 49)) else (if i.val < 142 then (if i.val < 141 then 54 else 46) else (if i.val < 143 then 46 else 55)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 46 else 25) else (if i.val < 147 then 47 else 25)) else (if i.val < 150 then (if i.val < 149 then 46 else 46) else (if i.val < 151 then 46 else 26))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 12 else 47) else (if i.val < 155 then 25 else 25)) else (if i.val < 158 then (if i.val < 157 then 46 else 12) else (if i.val < 159 then 46 else 46))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 49 else 49) else (if i.val < 163 then 47 else 46)) else (if i.val < 166 then (if i.val < 165 then 49 else 10) else (if i.val < 167 then 84 else 84))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 46 else 49) else (if i.val < 171 then 25 else 47)) else (if i.val < 174 then (if i.val < 173 then 49 else 49) else (if i.val < 175 then 27 else 46)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 46 else 49) else (if i.val < 179 then 49 else 54)) else (if i.val < 182 then (if i.val < 181 then 12 else 55) else (if i.val < 183 then 45 else 50))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 46 else 80) else (if i.val < 187 then 46 else 12)) else (if i.val < 190 then (if i.val < 189 then 45 else 49) else (if i.val < 191 then 47 else 46)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 49 else 46) else (if i.val < 195 then 46 else 25)) else (if i.val < 198 then (if i.val < 197 then 26 else 46) else (if i.val < 199 then 26 else 25))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 49 else 46) else (if i.val < 203 then 53 else 49)) else (if i.val < 206 then (if i.val < 205 then 49 else 26) else (if i.val < 207 then 13 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 47 else 12) else (if i.val < 211 then 46 else 50)) else (if i.val < 214 then (if i.val < 213 then 13 else 86) else (if i.val < 215 then 49 else 46))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 47 else 46) else (if i.val < 219 then 49 else 46)) else (if i.val < 222 then (if i.val < 221 then 55 else 25) else (if i.val < 223 then 46 else 56))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 48 else 47) else (if i.val < 227 then 50 else 49)) else (if i.val < 230 then (if i.val < 229 then 50 else 47) else (if i.val < 231 then 46 else 55))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 80 else 46) else (if i.val < 235 then 12 else 49)) else (if i.val < 238 then (if i.val < 237 then 46 else 13) else (if i.val < 239 then 46 else 46)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 26 else 84) else (if i.val < 243 then 49 else 46)) else (if i.val < 246 then (if i.val < 245 then 46 else 54) else (if i.val < 247 then 49 else 46))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 10 else 45) else (if i.val < 251 then 46 else 46)) else (if i.val < 254 then (if i.val < 253 then 46 else 46) else (if i.val < 255 then 46 else 46))))))))

theorem g32p_supplierForest_actual_097 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_097 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_097 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_072391
  · exact g32p_supplierForest_actual_072413
  · exact g32p_supplierForest_actual_072428
  · exact g32p_supplierForest_actual_072520
  · exact g32p_supplierForest_actual_072534
  · exact g32p_supplierForest_actual_072535
  · exact g32p_supplierForest_actual_072543
  · exact g32p_supplierForest_actual_072547
  · exact g32p_supplierForest_actual_072550
  · exact g32p_supplierForest_actual_072586
  · exact g32p_supplierForest_actual_072625
  · exact g32p_supplierForest_actual_072645
  · exact g32p_supplierForest_actual_072651
  · exact g32p_supplierForest_actual_072700
  · exact g32p_supplierForest_actual_072743
  · exact g32p_supplierForest_actual_072806
  · exact g32p_supplierForest_actual_072810
  · exact g32p_supplierForest_actual_072864
  · exact g32p_supplierForest_actual_072879
  · exact g32p_supplierForest_actual_072896
  · exact g32p_supplierForest_actual_072906
  · exact g32p_supplierForest_actual_072939
  · exact g32p_supplierForest_actual_072944
  · exact g32p_supplierForest_actual_072956
  · exact g32p_supplierForest_actual_072959
  · exact g32p_supplierForest_actual_072969
  · exact g32p_supplierForest_actual_072989
  · exact g32p_supplierForest_actual_072990
  · exact g32p_supplierForest_actual_073046
  · exact g32p_supplierForest_actual_073060
  · exact g32p_supplierForest_actual_073072
  · exact g32p_supplierForest_actual_073084
  · exact g32p_supplierForest_actual_073088
  · exact g32p_supplierForest_actual_073092
  · exact g32p_supplierForest_actual_073112
  · exact g32p_supplierForest_actual_073131
  · exact g32p_supplierForest_actual_073133
  · exact g32p_supplierForest_actual_073150
  · exact g32p_supplierForest_actual_073204
  · exact g32p_supplierForest_actual_073218
  · exact g32p_supplierForest_actual_073230
  · exact g32p_supplierForest_actual_073254
  · exact g32p_supplierForest_actual_073273
  · exact g32p_supplierForest_actual_073276
  · exact g32p_supplierForest_actual_073288
  · exact g32p_supplierForest_actual_073307
  · exact g32p_supplierForest_actual_073310
  · exact g32p_supplierForest_actual_073396
  · exact g32p_supplierForest_actual_073420
  · exact g32p_supplierForest_actual_073441
  · exact g32p_supplierForest_actual_073456
  · exact g32p_supplierForest_actual_073459
  · exact g32p_supplierForest_actual_073472
  · exact g32p_supplierForest_actual_073503
  · exact g32p_supplierForest_actual_073506
  · exact g32p_supplierForest_actual_073521
  · exact g32p_supplierForest_actual_073559
  · exact g32p_supplierForest_actual_073578
  · exact g32p_supplierForest_actual_073612
  · exact g32p_supplierForest_actual_073626
  · exact g32p_supplierForest_actual_073676
  · exact g32p_supplierForest_actual_073690
  · exact g32p_supplierForest_actual_073700
  · exact g32p_supplierForest_actual_073720
  · exact g32p_supplierForest_actual_073744
  · exact g32p_supplierForest_actual_073790
  · exact g32p_supplierForest_actual_073798
  · exact g32p_supplierForest_actual_073808
  · exact g32p_supplierForest_actual_073851
  · exact g32p_supplierForest_actual_073871
  · exact g32p_supplierForest_actual_073912
  · exact g32p_supplierForest_actual_073960
  · exact g32p_supplierForest_actual_073966
  · exact g32p_supplierForest_actual_073973
  · exact g32p_supplierForest_actual_073977
  · exact g32p_supplierForest_actual_073981
  · exact g32p_supplierForest_actual_073982
  · exact g32p_supplierForest_actual_073996
  · exact g32p_supplierForest_actual_073999
  · exact g32p_supplierForest_actual_074015
  · exact g32p_supplierForest_actual_074042
  · exact g32p_supplierForest_actual_074055
  · exact g32p_supplierForest_actual_074059
  · exact g32p_supplierForest_actual_074073
  · exact g32p_supplierForest_actual_074080
  · exact g32p_supplierForest_actual_074128
  · exact g32p_supplierForest_actual_074130
  · exact g32p_supplierForest_actual_074138
  · exact g32p_supplierForest_actual_074177
  · exact g32p_supplierForest_actual_074202
  · exact g32p_supplierForest_actual_074207
  · exact g32p_supplierForest_actual_074228
  · exact g32p_supplierForest_actual_074236
  · exact g32p_supplierForest_actual_074251
  · exact g32p_supplierForest_actual_074300
  · exact g32p_supplierForest_actual_074314
  · exact g32p_supplierForest_actual_074335
  · exact g32p_supplierForest_actual_074359
  · exact g32p_supplierForest_actual_074364
  · exact g32p_supplierForest_actual_074375
  · exact g32p_supplierForest_actual_074379
  · exact g32p_supplierForest_actual_074410
  · exact g32p_supplierForest_actual_074473
  · exact g32p_supplierForest_actual_074507
  · exact g32p_supplierForest_actual_074521
  · exact g32p_supplierForest_actual_074523
  · exact g32p_supplierForest_actual_074553
  · exact g32p_supplierForest_actual_074554
  · exact g32p_supplierForest_actual_074577
  · exact g32p_supplierForest_actual_074581
  · exact g32p_supplierForest_actual_074616
  · exact g32p_supplierForest_actual_074622
  · exact g32p_supplierForest_actual_074680
  · exact g32p_supplierForest_actual_074694
  · exact g32p_supplierForest_actual_074701
  · exact g32p_supplierForest_actual_074712
  · exact g32p_supplierForest_actual_074745
  · exact g32p_supplierForest_actual_074773
  · exact g32p_supplierForest_actual_074796
  · exact g32p_supplierForest_actual_074806
  · exact g32p_supplierForest_actual_074822
  · exact g32p_supplierForest_actual_074839
  · exact g32p_supplierForest_actual_074846
  · exact g32p_supplierForest_actual_074857
  · exact g32p_supplierForest_actual_074862
  · exact g32p_supplierForest_actual_074880
  · exact g32p_supplierForest_actual_074909
  · exact g32p_supplierForest_actual_074918
  · exact g32p_supplierForest_actual_074922
  · exact g32p_supplierForest_actual_074938
  · exact g32p_supplierForest_actual_074969
  · exact g32p_supplierForest_actual_075026
  · exact g32p_supplierForest_actual_075032
  · exact g32p_supplierForest_actual_075082
  · exact g32p_supplierForest_actual_075093
  · exact g32p_supplierForest_actual_075094
  · exact g32p_supplierForest_actual_075098
  · exact g32p_supplierForest_actual_075121
  · exact g32p_supplierForest_actual_075167
  · exact g32p_supplierForest_actual_075177
  · exact g32p_supplierForest_actual_075199
  · exact g32p_supplierForest_actual_075201
  · exact g32p_supplierForest_actual_075213
  · exact g32p_supplierForest_actual_075220
  · exact g32p_supplierForest_actual_075254
  · exact g32p_supplierForest_actual_075332
  · exact g32p_supplierForest_actual_075342
  · exact g32p_supplierForest_actual_075343
  · exact g32p_supplierForest_actual_075353
  · exact g32p_supplierForest_actual_075379
  · exact g32p_supplierForest_actual_075387
  · exact g32p_supplierForest_actual_075399
  · exact g32p_supplierForest_actual_075412
  · exact g32p_supplierForest_actual_075425
  · exact g32p_supplierForest_actual_075437
  · exact g32p_supplierForest_actual_075439
  · exact g32p_supplierForest_actual_075461
  · exact g32p_supplierForest_actual_075553
  · exact g32p_supplierForest_actual_075558
  · exact g32p_supplierForest_actual_075571
  · exact g32p_supplierForest_actual_075609
  · exact g32p_supplierForest_actual_075627
  · exact g32p_supplierForest_actual_075660
  · exact g32p_supplierForest_actual_075663
  · exact g32p_supplierForest_actual_075702
  · exact g32p_supplierForest_actual_075708
  · exact g32p_supplierForest_actual_075721
  · exact g32p_supplierForest_actual_075725
  · exact g32p_supplierForest_actual_075730
  · exact g32p_supplierForest_actual_075747
  · exact g32p_supplierForest_actual_075749
  · exact g32p_supplierForest_actual_075757
  · exact g32p_supplierForest_actual_075790
  · exact g32p_supplierForest_actual_075830
  · exact g32p_supplierForest_actual_075843
  · exact g32p_supplierForest_actual_075856
  · exact g32p_supplierForest_actual_075871
  · exact g32p_supplierForest_actual_075879
  · exact g32p_supplierForest_actual_075900
  · exact g32p_supplierForest_actual_075901
  · exact g32p_supplierForest_actual_075915
  · exact g32p_supplierForest_actual_075922
  · exact g32p_supplierForest_actual_075934
  · exact g32p_supplierForest_actual_075950
  · exact g32p_supplierForest_actual_075991
  · exact g32p_supplierForest_actual_075998
  · exact g32p_supplierForest_actual_076002
  · exact g32p_supplierForest_actual_076041
  · exact g32p_supplierForest_actual_076057
  · exact g32p_supplierForest_actual_076075
  · exact g32p_supplierForest_actual_076116
  · exact g32p_supplierForest_actual_076136
  · exact g32p_supplierForest_actual_076152
  · exact g32p_supplierForest_actual_076222
  · exact g32p_supplierForest_actual_076231
  · exact g32p_supplierForest_actual_076248
  · exact g32p_supplierForest_actual_076253
  · exact g32p_supplierForest_actual_076387
  · exact g32p_supplierForest_actual_076409
  · exact g32p_supplierForest_actual_076417
  · exact g32p_supplierForest_actual_076419
  · exact g32p_supplierForest_actual_076424
  · exact g32p_supplierForest_actual_076454
  · exact g32p_supplierForest_actual_076490
  · exact g32p_supplierForest_actual_076524
  · exact g32p_supplierForest_actual_076536
  · exact g32p_supplierForest_actual_076549
  · exact g32p_supplierForest_actual_076575
  · exact g32p_supplierForest_actual_076581
  · exact g32p_supplierForest_actual_076595
  · exact g32p_supplierForest_actual_076609
  · exact g32p_supplierForest_actual_076611
  · exact g32p_supplierForest_actual_076708
  · exact g32p_supplierForest_actual_076724
  · exact g32p_supplierForest_actual_076733
  · exact g32p_supplierForest_actual_076742
  · exact g32p_supplierForest_actual_076757
  · exact g32p_supplierForest_actual_076827
  · exact g32p_supplierForest_actual_076828
  · exact g32p_supplierForest_actual_076830
  · exact g32p_supplierForest_actual_076874
  · exact g32p_supplierForest_actual_076876
  · exact g32p_supplierForest_actual_076885
  · exact g32p_supplierForest_actual_076888
  · exact g32p_supplierForest_actual_076906
  · exact g32p_supplierForest_actual_076908
  · exact g32p_supplierForest_actual_076915
  · exact g32p_supplierForest_actual_076935
  · exact g32p_supplierForest_actual_076941
  · exact g32p_supplierForest_actual_076947
  · exact g32p_supplierForest_actual_076949
  · exact g32p_supplierForest_actual_076951
  · exact g32p_supplierForest_actual_076969
  · exact g32p_supplierForest_actual_076977
  · exact g32p_supplierForest_actual_076993
  · exact g32p_supplierForest_actual_077006
  · exact g32p_supplierForest_actual_077008
  · exact g32p_supplierForest_actual_077057
  · exact g32p_supplierForest_actual_077139
  · exact g32p_supplierForest_actual_077141
  · exact g32p_supplierForest_actual_077201
  · exact g32p_supplierForest_actual_077212
  · exact g32p_supplierForest_actual_077222
  · exact g32p_supplierForest_actual_077251
  · exact g32p_supplierForest_actual_077255
  · exact g32p_supplierForest_actual_077288
  · exact g32p_supplierForest_actual_077428
  · exact g32p_supplierForest_actual_077446
  · exact g32p_supplierForest_actual_077467
  · exact g32p_supplierForest_actual_077497
  · exact g32p_supplierForest_actual_077525
  · exact g32p_supplierForest_actual_077527
  · exact g32p_supplierForest_actual_077532
  · exact g32p_supplierForest_actual_077559
  · exact g32p_supplierForest_actual_077561
  · exact g32p_supplierForest_actual_077569

def g32p_supplierForest_nodes_098 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_077593 else g32p_supplierForest_node_077603) else (if i.val < 3 then g32p_supplierForest_node_077618 else g32p_supplierForest_node_077626)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_077664 else g32p_supplierForest_node_077672) else (if i.val < 7 then g32p_supplierForest_node_077756 else g32p_supplierForest_node_077772))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_077781 else g32p_supplierForest_node_077785) else (if i.val < 11 then g32p_supplierForest_node_077812 else g32p_supplierForest_node_077848)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_077866 else g32p_supplierForest_node_077893) else (if i.val < 15 then g32p_supplierForest_node_077927 else g32p_supplierForest_node_077991)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_078002 else g32p_supplierForest_node_078010) else (if i.val < 19 then g32p_supplierForest_node_078021 else g32p_supplierForest_node_078057)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_078068 else g32p_supplierForest_node_078100) else (if i.val < 23 then g32p_supplierForest_node_078128 else g32p_supplierForest_node_078133))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_078141 else g32p_supplierForest_node_078151) else (if i.val < 27 then g32p_supplierForest_node_078152 else g32p_supplierForest_node_078172)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_078220 else g32p_supplierForest_node_078224) else (if i.val < 31 then g32p_supplierForest_node_078283 else g32p_supplierForest_node_078377))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_078402 else g32p_supplierForest_node_078406) else (if i.val < 35 then g32p_supplierForest_node_078415 else g32p_supplierForest_node_078419)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_078423 else g32p_supplierForest_node_078430) else (if i.val < 39 then g32p_supplierForest_node_078483 else g32p_supplierForest_node_078509))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_078539 else g32p_supplierForest_node_078579) else (if i.val < 43 then g32p_supplierForest_node_078586 else g32p_supplierForest_node_078608)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_078613 else g32p_supplierForest_node_078624) else (if i.val < 47 then g32p_supplierForest_node_078630 else g32p_supplierForest_node_078654)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_078656 else g32p_supplierForest_node_078662) else (if i.val < 51 then g32p_supplierForest_node_078693 else g32p_supplierForest_node_078709)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_078726 else g32p_supplierForest_node_078743) else (if i.val < 55 then g32p_supplierForest_node_078756 else g32p_supplierForest_node_078758))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_078778 else g32p_supplierForest_node_078788) else (if i.val < 59 then g32p_supplierForest_node_078828 else g32p_supplierForest_node_078928)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_078929 else g32p_supplierForest_node_078945) else (if i.val < 63 then g32p_supplierForest_node_078951 else g32p_supplierForest_node_078980)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_078981 else g32p_supplierForest_node_079055) else (if i.val < 67 then g32p_supplierForest_node_079072 else g32p_supplierForest_node_079090)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_079126 else g32p_supplierForest_node_079157) else (if i.val < 71 then g32p_supplierForest_node_079161 else g32p_supplierForest_node_079200))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_079232 else g32p_supplierForest_node_079274) else (if i.val < 75 then g32p_supplierForest_node_079300 else g32p_supplierForest_node_079302)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_079307 else g32p_supplierForest_node_079313) else (if i.val < 79 then g32p_supplierForest_node_079345 else g32p_supplierForest_node_079376)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_079380 else g32p_supplierForest_node_079383) else (if i.val < 83 then g32p_supplierForest_node_079447 else g32p_supplierForest_node_079576)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_079630 else g32p_supplierForest_node_079647) else (if i.val < 87 then g32p_supplierForest_node_079656 else g32p_supplierForest_node_079672))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_079696 else g32p_supplierForest_node_079698) else (if i.val < 91 then g32p_supplierForest_node_079828 else g32p_supplierForest_node_079908)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_079922 else g32p_supplierForest_node_079945) else (if i.val < 95 then g32p_supplierForest_node_079954 else g32p_supplierForest_node_080001))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_080032 else g32p_supplierForest_node_080034) else (if i.val < 99 then g32p_supplierForest_node_080045 else g32p_supplierForest_node_080062)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_080089 else g32p_supplierForest_node_080096) else (if i.val < 103 then g32p_supplierForest_node_080149 else g32p_supplierForest_node_080191))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_080211 else g32p_supplierForest_node_080214) else (if i.val < 107 then g32p_supplierForest_node_080239 else g32p_supplierForest_node_080267)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_080276 else g32p_supplierForest_node_080321) else (if i.val < 111 then g32p_supplierForest_node_080326 else g32p_supplierForest_node_080336)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_080368 else g32p_supplierForest_node_080380) else (if i.val < 115 then g32p_supplierForest_node_080423 else g32p_supplierForest_node_080439)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_080445 else g32p_supplierForest_node_080446) else (if i.val < 119 then g32p_supplierForest_node_080453 else g32p_supplierForest_node_080466))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_080477 else g32p_supplierForest_node_080497) else (if i.val < 123 then g32p_supplierForest_node_080530 else g32p_supplierForest_node_080564)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_080565 else g32p_supplierForest_node_080690) else (if i.val < 127 then g32p_supplierForest_node_080695 else g32p_supplierForest_node_080701))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_080779 else g32p_supplierForest_node_080805) else (if i.val < 131 then g32p_supplierForest_node_080819 else g32p_supplierForest_node_080855)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_080856 else g32p_supplierForest_node_080898) else (if i.val < 135 then g32p_supplierForest_node_080899 else g32p_supplierForest_node_080999))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_081000 else g32p_supplierForest_node_081014) else (if i.val < 139 then g32p_supplierForest_node_081046 else g32p_supplierForest_node_081111)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_081117 else g32p_supplierForest_node_081120) else (if i.val < 143 then g32p_supplierForest_node_081139 else g32p_supplierForest_node_081157)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_081163 else g32p_supplierForest_node_081213) else (if i.val < 147 then g32p_supplierForest_node_081238 else g32p_supplierForest_node_081250)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_081267 else g32p_supplierForest_node_081322) else (if i.val < 151 then g32p_supplierForest_node_081338 else g32p_supplierForest_node_081344))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_081357 else g32p_supplierForest_node_081374) else (if i.val < 155 then g32p_supplierForest_node_081393 else g32p_supplierForest_node_081419)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_081454 else g32p_supplierForest_node_081468) else (if i.val < 159 then g32p_supplierForest_node_081476 else g32p_supplierForest_node_081523))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_081545 else g32p_supplierForest_node_081547) else (if i.val < 163 then g32p_supplierForest_node_081558 else g32p_supplierForest_node_081562)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_081577 else g32p_supplierForest_node_081591) else (if i.val < 167 then g32p_supplierForest_node_081613 else g32p_supplierForest_node_081623))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_081633 else g32p_supplierForest_node_081637) else (if i.val < 171 then g32p_supplierForest_node_081648 else g32p_supplierForest_node_081651)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_081655 else g32p_supplierForest_node_081678) else (if i.val < 175 then g32p_supplierForest_node_081679 else g32p_supplierForest_node_081684)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_081705 else g32p_supplierForest_node_081760) else (if i.val < 179 then g32p_supplierForest_node_081761 else g32p_supplierForest_node_081788)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_081804 else g32p_supplierForest_node_081808) else (if i.val < 183 then g32p_supplierForest_node_081812 else g32p_supplierForest_node_081818))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_081825 else g32p_supplierForest_node_081883) else (if i.val < 187 then g32p_supplierForest_node_081894 else g32p_supplierForest_node_081947)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_081964 else g32p_supplierForest_node_081966) else (if i.val < 191 then g32p_supplierForest_node_082007 else g32p_supplierForest_node_082015)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_082031 else g32p_supplierForest_node_082066) else (if i.val < 195 then g32p_supplierForest_node_082073 else g32p_supplierForest_node_082087)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_082092 else g32p_supplierForest_node_082100) else (if i.val < 199 then g32p_supplierForest_node_082124 else g32p_supplierForest_node_082131))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_082146 else g32p_supplierForest_node_082209) else (if i.val < 203 then g32p_supplierForest_node_082219 else g32p_supplierForest_node_082222)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_082254 else g32p_supplierForest_node_082309) else (if i.val < 207 then g32p_supplierForest_node_082320 else g32p_supplierForest_node_082343)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_082358 else g32p_supplierForest_node_082423) else (if i.val < 211 then g32p_supplierForest_node_082455 else g32p_supplierForest_node_082462)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_082485 else g32p_supplierForest_node_082512) else (if i.val < 215 then g32p_supplierForest_node_082555 else g32p_supplierForest_node_082566))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_082624 else g32p_supplierForest_node_082641) else (if i.val < 219 then g32p_supplierForest_node_082647 else g32p_supplierForest_node_082656)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_082657 else g32p_supplierForest_node_082671) else (if i.val < 223 then g32p_supplierForest_node_082674 else g32p_supplierForest_node_082701))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_082745 else g32p_supplierForest_node_082764) else (if i.val < 227 then g32p_supplierForest_node_082785 else g32p_supplierForest_node_082811)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_082833 else g32p_supplierForest_node_082846) else (if i.val < 231 then g32p_supplierForest_node_082867 else g32p_supplierForest_node_082868))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_082873 else g32p_supplierForest_node_082874) else (if i.val < 235 then g32p_supplierForest_node_082875 else g32p_supplierForest_node_082883)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_082884 else g32p_supplierForest_node_082904) else (if i.val < 239 then g32p_supplierForest_node_082970 else g32p_supplierForest_node_082981)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_083034 else g32p_supplierForest_node_083050) else (if i.val < 243 then g32p_supplierForest_node_083053 else g32p_supplierForest_node_083097)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_083115 else g32p_supplierForest_node_083133) else (if i.val < 247 then g32p_supplierForest_node_083137 else g32p_supplierForest_node_083176))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_083177 else g32p_supplierForest_node_083189) else (if i.val < 251 then g32p_supplierForest_node_083190 else g32p_supplierForest_node_083201)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_083226 else g32p_supplierForest_node_083228) else (if i.val < 255 then g32p_supplierForest_node_083245 else g32p_supplierForest_node_083246))))))))

def g32p_supplierForest_classes_098 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 50 else 26) else (if i.val < 3 then 49 else 25)) else (if i.val < 6 then (if i.val < 5 then 26 else 46) else (if i.val < 7 then 26 else 49))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 84 else 46) else (if i.val < 11 then 45 else 84)) else (if i.val < 14 then (if i.val < 13 then 84 else 46) else (if i.val < 15 then 46 else 84)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 46 else 45) else (if i.val < 19 then 9 else 46)) else (if i.val < 22 then (if i.val < 21 then 45 else 46) else (if i.val < 23 then 55 else 47))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 26 else 49) else (if i.val < 27 then 49 else 54)) else (if i.val < 30 then (if i.val < 29 then 49 else 46) else (if i.val < 31 then 49 else 84))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 46 else 84) else (if i.val < 35 then 46 else 47)) else (if i.val < 38 then (if i.val < 37 then 49 else 49) else (if i.val < 39 then 45 else 25))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 12 else 26) else (if i.val < 43 then 9 else 46)) else (if i.val < 46 then (if i.val < 45 then 50 else 84) else (if i.val < 47 then 50 else 45)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 9 else 46) else (if i.val < 51 then 26 else 25)) else (if i.val < 54 then (if i.val < 53 then 47 else 10) else (if i.val < 55 then 9 else 45))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 46 else 86) else (if i.val < 59 then 9 else 46)) else (if i.val < 62 then (if i.val < 61 then 46 else 25) else (if i.val < 63 then 9 else 45)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 46 else 49) else (if i.val < 67 then 25 else 46)) else (if i.val < 70 then (if i.val < 69 then 83 else 9) else (if i.val < 71 then 10 else 49))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 46 else 9) else (if i.val < 75 then 54 else 47)) else (if i.val < 78 then (if i.val < 77 then 26 else 26) else (if i.val < 79 then 46 else 47)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 26 else 12) else (if i.val < 83 then 47 else 49)) else (if i.val < 86 then (if i.val < 85 then 49 else 46) else (if i.val < 87 then 49 else 54))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 25 else 83) else (if i.val < 91 then 83 else 26)) else (if i.val < 94 then (if i.val < 93 then 50 else 49) else (if i.val < 95 then 49 else 49))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 47 else 49) else (if i.val < 99 then 49 else 13)) else (if i.val < 102 then (if i.val < 101 then 9 else 85) else (if i.val < 103 then 46 else 47))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 26 else 47) else (if i.val < 107 then 49 else 50)) else (if i.val < 110 then (if i.val < 109 then 46 else 49) else (if i.val < 111 then 50 else 26)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 26 else 49) else (if i.val < 115 then 49 else 50)) else (if i.val < 118 then (if i.val < 117 then 50 else 49) else (if i.val < 119 then 49 else 27))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 26 else 49) else (if i.val < 123 then 46 else 26)) else (if i.val < 126 then (if i.val < 125 then 25 else 12) else (if i.val < 127 then 12 else 49))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 49) else (if i.val < 131 then 47 else 46)) else (if i.val < 134 then (if i.val < 133 then 26 else 54) else (if i.val < 135 then 49 else 26))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 80 else 55) else (if i.val < 139 then 50 else 83)) else (if i.val < 142 then (if i.val < 141 then 49 else 9) else (if i.val < 143 then 49 else 27)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 47 else 46) else (if i.val < 147 then 26 else 83)) else (if i.val < 150 then (if i.val < 149 then 49 else 84) else (if i.val < 151 then 49 else 26))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 25 else 25) else (if i.val < 155 then 49 else 25)) else (if i.val < 158 then (if i.val < 157 then 9 else 52) else (if i.val < 159 then 55 else 10))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 9 else 49) else (if i.val < 163 then 49 else 46)) else (if i.val < 166 then (if i.val < 165 then 25 else 27) else (if i.val < 167 then 49 else 46))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 50 else 48) else (if i.val < 171 then 49 else 49)) else (if i.val < 174 then (if i.val < 173 then 48 else 49) else (if i.val < 175 then 46 else 49)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 47 else 49) else (if i.val < 179 then 55 else 46)) else (if i.val < 182 then (if i.val < 181 then 49 else 46) else (if i.val < 183 then 52 else 47))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 49) else (if i.val < 187 then 13 else 49)) else (if i.val < 190 then (if i.val < 189 then 52 else 46) else (if i.val < 191 then 49 else 13)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 10 else 46) else (if i.val < 195 then 46 else 49)) else (if i.val < 198 then (if i.val < 197 then 25 else 49) else (if i.val < 199 then 46 else 46))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 49 else 49) else (if i.val < 203 then 48 else 12)) else (if i.val < 206 then (if i.val < 205 then 46 else 46) else (if i.val < 207 then 47 else 47)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 46 else 12) else (if i.val < 211 then 45 else 49)) else (if i.val < 214 then (if i.val < 213 then 26 else 49) else (if i.val < 215 then 47 else 46))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 46 else 56) else (if i.val < 219 then 10 else 49)) else (if i.val < 222 then (if i.val < 221 then 49 else 46) else (if i.val < 223 then 49 else 46))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 49 else 49) else (if i.val < 227 then 46 else 46)) else (if i.val < 230 then (if i.val < 229 then 12 else 47) else (if i.val < 231 then 49 else 46))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 46 else 48) else (if i.val < 235 then 46 else 48)) else (if i.val < 238 then (if i.val < 237 then 49 else 12) else (if i.val < 239 then 49 else 25)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 45 else 86) else (if i.val < 243 then 49 else 46)) else (if i.val < 246 then (if i.val < 245 then 50 else 46) else (if i.val < 247 then 84 else 80))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 47) else (if i.val < 251 then 55 else 50)) else (if i.val < 254 then (if i.val < 253 then 49 else 46) else (if i.val < 255 then 46 else 46))))))))

theorem g32p_supplierForest_actual_098 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_098 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_098 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_077593
  · exact g32p_supplierForest_actual_077603
  · exact g32p_supplierForest_actual_077618
  · exact g32p_supplierForest_actual_077626
  · exact g32p_supplierForest_actual_077664
  · exact g32p_supplierForest_actual_077672
  · exact g32p_supplierForest_actual_077756
  · exact g32p_supplierForest_actual_077772
  · exact g32p_supplierForest_actual_077781
  · exact g32p_supplierForest_actual_077785
  · exact g32p_supplierForest_actual_077812
  · exact g32p_supplierForest_actual_077848
  · exact g32p_supplierForest_actual_077866
  · exact g32p_supplierForest_actual_077893
  · exact g32p_supplierForest_actual_077927
  · exact g32p_supplierForest_actual_077991
  · exact g32p_supplierForest_actual_078002
  · exact g32p_supplierForest_actual_078010
  · exact g32p_supplierForest_actual_078021
  · exact g32p_supplierForest_actual_078057
  · exact g32p_supplierForest_actual_078068
  · exact g32p_supplierForest_actual_078100
  · exact g32p_supplierForest_actual_078128
  · exact g32p_supplierForest_actual_078133
  · exact g32p_supplierForest_actual_078141
  · exact g32p_supplierForest_actual_078151
  · exact g32p_supplierForest_actual_078152
  · exact g32p_supplierForest_actual_078172
  · exact g32p_supplierForest_actual_078220
  · exact g32p_supplierForest_actual_078224
  · exact g32p_supplierForest_actual_078283
  · exact g32p_supplierForest_actual_078377
  · exact g32p_supplierForest_actual_078402
  · exact g32p_supplierForest_actual_078406
  · exact g32p_supplierForest_actual_078415
  · exact g32p_supplierForest_actual_078419
  · exact g32p_supplierForest_actual_078423
  · exact g32p_supplierForest_actual_078430
  · exact g32p_supplierForest_actual_078483
  · exact g32p_supplierForest_actual_078509
  · exact g32p_supplierForest_actual_078539
  · exact g32p_supplierForest_actual_078579
  · exact g32p_supplierForest_actual_078586
  · exact g32p_supplierForest_actual_078608
  · exact g32p_supplierForest_actual_078613
  · exact g32p_supplierForest_actual_078624
  · exact g32p_supplierForest_actual_078630
  · exact g32p_supplierForest_actual_078654
  · exact g32p_supplierForest_actual_078656
  · exact g32p_supplierForest_actual_078662
  · exact g32p_supplierForest_actual_078693
  · exact g32p_supplierForest_actual_078709
  · exact g32p_supplierForest_actual_078726
  · exact g32p_supplierForest_actual_078743
  · exact g32p_supplierForest_actual_078756
  · exact g32p_supplierForest_actual_078758
  · exact g32p_supplierForest_actual_078778
  · exact g32p_supplierForest_actual_078788
  · exact g32p_supplierForest_actual_078828
  · exact g32p_supplierForest_actual_078928
  · exact g32p_supplierForest_actual_078929
  · exact g32p_supplierForest_actual_078945
  · exact g32p_supplierForest_actual_078951
  · exact g32p_supplierForest_actual_078980
  · exact g32p_supplierForest_actual_078981
  · exact g32p_supplierForest_actual_079055
  · exact g32p_supplierForest_actual_079072
  · exact g32p_supplierForest_actual_079090
  · exact g32p_supplierForest_actual_079126
  · exact g32p_supplierForest_actual_079157
  · exact g32p_supplierForest_actual_079161
  · exact g32p_supplierForest_actual_079200
  · exact g32p_supplierForest_actual_079232
  · exact g32p_supplierForest_actual_079274
  · exact g32p_supplierForest_actual_079300
  · exact g32p_supplierForest_actual_079302
  · exact g32p_supplierForest_actual_079307
  · exact g32p_supplierForest_actual_079313
  · exact g32p_supplierForest_actual_079345
  · exact g32p_supplierForest_actual_079376
  · exact g32p_supplierForest_actual_079380
  · exact g32p_supplierForest_actual_079383
  · exact g32p_supplierForest_actual_079447
  · exact g32p_supplierForest_actual_079576
  · exact g32p_supplierForest_actual_079630
  · exact g32p_supplierForest_actual_079647
  · exact g32p_supplierForest_actual_079656
  · exact g32p_supplierForest_actual_079672
  · exact g32p_supplierForest_actual_079696
  · exact g32p_supplierForest_actual_079698
  · exact g32p_supplierForest_actual_079828
  · exact g32p_supplierForest_actual_079908
  · exact g32p_supplierForest_actual_079922
  · exact g32p_supplierForest_actual_079945
  · exact g32p_supplierForest_actual_079954
  · exact g32p_supplierForest_actual_080001
  · exact g32p_supplierForest_actual_080032
  · exact g32p_supplierForest_actual_080034
  · exact g32p_supplierForest_actual_080045
  · exact g32p_supplierForest_actual_080062
  · exact g32p_supplierForest_actual_080089
  · exact g32p_supplierForest_actual_080096
  · exact g32p_supplierForest_actual_080149
  · exact g32p_supplierForest_actual_080191
  · exact g32p_supplierForest_actual_080211
  · exact g32p_supplierForest_actual_080214
  · exact g32p_supplierForest_actual_080239
  · exact g32p_supplierForest_actual_080267
  · exact g32p_supplierForest_actual_080276
  · exact g32p_supplierForest_actual_080321
  · exact g32p_supplierForest_actual_080326
  · exact g32p_supplierForest_actual_080336
  · exact g32p_supplierForest_actual_080368
  · exact g32p_supplierForest_actual_080380
  · exact g32p_supplierForest_actual_080423
  · exact g32p_supplierForest_actual_080439
  · exact g32p_supplierForest_actual_080445
  · exact g32p_supplierForest_actual_080446
  · exact g32p_supplierForest_actual_080453
  · exact g32p_supplierForest_actual_080466
  · exact g32p_supplierForest_actual_080477
  · exact g32p_supplierForest_actual_080497
  · exact g32p_supplierForest_actual_080530
  · exact g32p_supplierForest_actual_080564
  · exact g32p_supplierForest_actual_080565
  · exact g32p_supplierForest_actual_080690
  · exact g32p_supplierForest_actual_080695
  · exact g32p_supplierForest_actual_080701
  · exact g32p_supplierForest_actual_080779
  · exact g32p_supplierForest_actual_080805
  · exact g32p_supplierForest_actual_080819
  · exact g32p_supplierForest_actual_080855
  · exact g32p_supplierForest_actual_080856
  · exact g32p_supplierForest_actual_080898
  · exact g32p_supplierForest_actual_080899
  · exact g32p_supplierForest_actual_080999
  · exact g32p_supplierForest_actual_081000
  · exact g32p_supplierForest_actual_081014
  · exact g32p_supplierForest_actual_081046
  · exact g32p_supplierForest_actual_081111
  · exact g32p_supplierForest_actual_081117
  · exact g32p_supplierForest_actual_081120
  · exact g32p_supplierForest_actual_081139
  · exact g32p_supplierForest_actual_081157
  · exact g32p_supplierForest_actual_081163
  · exact g32p_supplierForest_actual_081213
  · exact g32p_supplierForest_actual_081238
  · exact g32p_supplierForest_actual_081250
  · exact g32p_supplierForest_actual_081267
  · exact g32p_supplierForest_actual_081322
  · exact g32p_supplierForest_actual_081338
  · exact g32p_supplierForest_actual_081344
  · exact g32p_supplierForest_actual_081357
  · exact g32p_supplierForest_actual_081374
  · exact g32p_supplierForest_actual_081393
  · exact g32p_supplierForest_actual_081419
  · exact g32p_supplierForest_actual_081454
  · exact g32p_supplierForest_actual_081468
  · exact g32p_supplierForest_actual_081476
  · exact g32p_supplierForest_actual_081523
  · exact g32p_supplierForest_actual_081545
  · exact g32p_supplierForest_actual_081547
  · exact g32p_supplierForest_actual_081558
  · exact g32p_supplierForest_actual_081562
  · exact g32p_supplierForest_actual_081577
  · exact g32p_supplierForest_actual_081591
  · exact g32p_supplierForest_actual_081613
  · exact g32p_supplierForest_actual_081623
  · exact g32p_supplierForest_actual_081633
  · exact g32p_supplierForest_actual_081637
  · exact g32p_supplierForest_actual_081648
  · exact g32p_supplierForest_actual_081651
  · exact g32p_supplierForest_actual_081655
  · exact g32p_supplierForest_actual_081678
  · exact g32p_supplierForest_actual_081679
  · exact g32p_supplierForest_actual_081684
  · exact g32p_supplierForest_actual_081705
  · exact g32p_supplierForest_actual_081760
  · exact g32p_supplierForest_actual_081761
  · exact g32p_supplierForest_actual_081788
  · exact g32p_supplierForest_actual_081804
  · exact g32p_supplierForest_actual_081808
  · exact g32p_supplierForest_actual_081812
  · exact g32p_supplierForest_actual_081818
  · exact g32p_supplierForest_actual_081825
  · exact g32p_supplierForest_actual_081883
  · exact g32p_supplierForest_actual_081894
  · exact g32p_supplierForest_actual_081947
  · exact g32p_supplierForest_actual_081964
  · exact g32p_supplierForest_actual_081966
  · exact g32p_supplierForest_actual_082007
  · exact g32p_supplierForest_actual_082015
  · exact g32p_supplierForest_actual_082031
  · exact g32p_supplierForest_actual_082066
  · exact g32p_supplierForest_actual_082073
  · exact g32p_supplierForest_actual_082087
  · exact g32p_supplierForest_actual_082092
  · exact g32p_supplierForest_actual_082100
  · exact g32p_supplierForest_actual_082124
  · exact g32p_supplierForest_actual_082131
  · exact g32p_supplierForest_actual_082146
  · exact g32p_supplierForest_actual_082209
  · exact g32p_supplierForest_actual_082219
  · exact g32p_supplierForest_actual_082222
  · exact g32p_supplierForest_actual_082254
  · exact g32p_supplierForest_actual_082309
  · exact g32p_supplierForest_actual_082320
  · exact g32p_supplierForest_actual_082343
  · exact g32p_supplierForest_actual_082358
  · exact g32p_supplierForest_actual_082423
  · exact g32p_supplierForest_actual_082455
  · exact g32p_supplierForest_actual_082462
  · exact g32p_supplierForest_actual_082485
  · exact g32p_supplierForest_actual_082512
  · exact g32p_supplierForest_actual_082555
  · exact g32p_supplierForest_actual_082566
  · exact g32p_supplierForest_actual_082624
  · exact g32p_supplierForest_actual_082641
  · exact g32p_supplierForest_actual_082647
  · exact g32p_supplierForest_actual_082656
  · exact g32p_supplierForest_actual_082657
  · exact g32p_supplierForest_actual_082671
  · exact g32p_supplierForest_actual_082674
  · exact g32p_supplierForest_actual_082701
  · exact g32p_supplierForest_actual_082745
  · exact g32p_supplierForest_actual_082764
  · exact g32p_supplierForest_actual_082785
  · exact g32p_supplierForest_actual_082811
  · exact g32p_supplierForest_actual_082833
  · exact g32p_supplierForest_actual_082846
  · exact g32p_supplierForest_actual_082867
  · exact g32p_supplierForest_actual_082868
  · exact g32p_supplierForest_actual_082873
  · exact g32p_supplierForest_actual_082874
  · exact g32p_supplierForest_actual_082875
  · exact g32p_supplierForest_actual_082883
  · exact g32p_supplierForest_actual_082884
  · exact g32p_supplierForest_actual_082904
  · exact g32p_supplierForest_actual_082970
  · exact g32p_supplierForest_actual_082981
  · exact g32p_supplierForest_actual_083034
  · exact g32p_supplierForest_actual_083050
  · exact g32p_supplierForest_actual_083053
  · exact g32p_supplierForest_actual_083097
  · exact g32p_supplierForest_actual_083115
  · exact g32p_supplierForest_actual_083133
  · exact g32p_supplierForest_actual_083137
  · exact g32p_supplierForest_actual_083176
  · exact g32p_supplierForest_actual_083177
  · exact g32p_supplierForest_actual_083189
  · exact g32p_supplierForest_actual_083190
  · exact g32p_supplierForest_actual_083201
  · exact g32p_supplierForest_actual_083226
  · exact g32p_supplierForest_actual_083228
  · exact g32p_supplierForest_actual_083245
  · exact g32p_supplierForest_actual_083246

def g32p_supplierForest_nodes_099 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_083253 else g32p_supplierForest_node_083291) else (if i.val < 3 then g32p_supplierForest_node_083301 else g32p_supplierForest_node_083329)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_083368 else g32p_supplierForest_node_083373) else (if i.val < 7 then g32p_supplierForest_node_083375 else g32p_supplierForest_node_083391))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_083409 else g32p_supplierForest_node_083427) else (if i.val < 11 then g32p_supplierForest_node_083430 else g32p_supplierForest_node_083438)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_083439 else g32p_supplierForest_node_083489) else (if i.val < 15 then g32p_supplierForest_node_083490 else g32p_supplierForest_node_083494)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_083555 else g32p_supplierForest_node_083567) else (if i.val < 19 then g32p_supplierForest_node_083568 else g32p_supplierForest_node_083664)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_083681 else g32p_supplierForest_node_083686) else (if i.val < 23 then g32p_supplierForest_node_083703 else g32p_supplierForest_node_083763))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_083769 else g32p_supplierForest_node_083797) else (if i.val < 27 then g32p_supplierForest_node_083806 else g32p_supplierForest_node_083837)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_083895 else g32p_supplierForest_node_083915) else (if i.val < 31 then g32p_supplierForest_node_083965 else g32p_supplierForest_node_084008))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_084013 else g32p_supplierForest_node_084022) else (if i.val < 35 then g32p_supplierForest_node_084025 else g32p_supplierForest_node_084035)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_084055 else g32p_supplierForest_node_084058) else (if i.val < 39 then g32p_supplierForest_node_084060 else g32p_supplierForest_node_084085))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_084088 else g32p_supplierForest_node_084096) else (if i.val < 43 then g32p_supplierForest_node_084166 else g32p_supplierForest_node_084237)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_084286 else g32p_supplierForest_node_084315) else (if i.val < 47 then g32p_supplierForest_node_084317 else g32p_supplierForest_node_084345)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_084379 else g32p_supplierForest_node_084390) else (if i.val < 51 then g32p_supplierForest_node_084414 else g32p_supplierForest_node_084444)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_084486 else g32p_supplierForest_node_084512) else (if i.val < 55 then g32p_supplierForest_node_084555 else g32p_supplierForest_node_084579))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_084596 else g32p_supplierForest_node_084626) else (if i.val < 59 then g32p_supplierForest_node_084633 else g32p_supplierForest_node_084639)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_084648 else g32p_supplierForest_node_084663) else (if i.val < 63 then g32p_supplierForest_node_084670 else g32p_supplierForest_node_084671)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_084716 else g32p_supplierForest_node_084738) else (if i.val < 67 then g32p_supplierForest_node_084742 else g32p_supplierForest_node_084750)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_084766 else g32p_supplierForest_node_084779) else (if i.val < 71 then g32p_supplierForest_node_084797 else g32p_supplierForest_node_084833))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_084853 else g32p_supplierForest_node_084881) else (if i.val < 75 then g32p_supplierForest_node_084931 else g32p_supplierForest_node_084933)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_084936 else g32p_supplierForest_node_084951) else (if i.val < 79 then g32p_supplierForest_node_084957 else g32p_supplierForest_node_084958)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_084976 else g32p_supplierForest_node_085105) else (if i.val < 83 then g32p_supplierForest_node_085120 else g32p_supplierForest_node_085144)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_085152 else g32p_supplierForest_node_085162) else (if i.val < 87 then g32p_supplierForest_node_085202 else g32p_supplierForest_node_085209))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_085232 else g32p_supplierForest_node_085243) else (if i.val < 91 then g32p_supplierForest_node_085250 else g32p_supplierForest_node_085286)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_085320 else g32p_supplierForest_node_085361) else (if i.val < 95 then g32p_supplierForest_node_085377 else g32p_supplierForest_node_085416))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_085433 else g32p_supplierForest_node_085435) else (if i.val < 99 then g32p_supplierForest_node_085444 else g32p_supplierForest_node_085447)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_085449 else g32p_supplierForest_node_085454) else (if i.val < 103 then g32p_supplierForest_node_085455 else g32p_supplierForest_node_085458))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_085491 else g32p_supplierForest_node_085494) else (if i.val < 107 then g32p_supplierForest_node_085534 else g32p_supplierForest_node_085557)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_085559 else g32p_supplierForest_node_085629) else (if i.val < 111 then g32p_supplierForest_node_085663 else g32p_supplierForest_node_085666)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_085683 else g32p_supplierForest_node_085687) else (if i.val < 115 then g32p_supplierForest_node_085726 else g32p_supplierForest_node_085740)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_085757 else g32p_supplierForest_node_085764) else (if i.val < 119 then g32p_supplierForest_node_085783 else g32p_supplierForest_node_085832))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_085847 else g32p_supplierForest_node_085870) else (if i.val < 123 then g32p_supplierForest_node_085879 else g32p_supplierForest_node_085885)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_085902 else g32p_supplierForest_node_085952) else (if i.val < 127 then g32p_supplierForest_node_086022 else g32p_supplierForest_node_086060))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_086068 else g32p_supplierForest_node_086085) else (if i.val < 131 then g32p_supplierForest_node_086088 else g32p_supplierForest_node_086128)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_086138 else g32p_supplierForest_node_086167) else (if i.val < 135 then g32p_supplierForest_node_086204 else g32p_supplierForest_node_086217))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_086230 else g32p_supplierForest_node_086270) else (if i.val < 139 then g32p_supplierForest_node_086300 else g32p_supplierForest_node_086324)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_086365 else g32p_supplierForest_node_086382) else (if i.val < 143 then g32p_supplierForest_node_086387 else g32p_supplierForest_node_086388)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_086430 else g32p_supplierForest_node_086433) else (if i.val < 147 then g32p_supplierForest_node_086457 else g32p_supplierForest_node_086465)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_086491 else g32p_supplierForest_node_086526) else (if i.val < 151 then g32p_supplierForest_node_086538 else g32p_supplierForest_node_086544))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_086591 else g32p_supplierForest_node_086617) else (if i.val < 155 then g32p_supplierForest_node_086618 else g32p_supplierForest_node_086662)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_086686 else g32p_supplierForest_node_086698) else (if i.val < 159 then g32p_supplierForest_node_086727 else g32p_supplierForest_node_086742))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_086801 else g32p_supplierForest_node_086803) else (if i.val < 163 then g32p_supplierForest_node_086809 else g32p_supplierForest_node_086832)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_086839 else g32p_supplierForest_node_086840) else (if i.val < 167 then g32p_supplierForest_node_086859 else g32p_supplierForest_node_086865))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_086877 else g32p_supplierForest_node_086885) else (if i.val < 171 then g32p_supplierForest_node_086892 else g32p_supplierForest_node_086905)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_086922 else g32p_supplierForest_node_086927) else (if i.val < 175 then g32p_supplierForest_node_086936 else g32p_supplierForest_node_086958)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_086961 else g32p_supplierForest_node_086963) else (if i.val < 179 then g32p_supplierForest_node_087021 else g32p_supplierForest_node_087040)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_087049 else g32p_supplierForest_node_087064) else (if i.val < 183 then g32p_supplierForest_node_087088 else g32p_supplierForest_node_087182))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_087192 else g32p_supplierForest_node_087194) else (if i.val < 187 then g32p_supplierForest_node_087208 else g32p_supplierForest_node_087225)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_087282 else g32p_supplierForest_node_087297) else (if i.val < 191 then g32p_supplierForest_node_087302 else g32p_supplierForest_node_087321)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_087327 else g32p_supplierForest_node_087364) else (if i.val < 195 then g32p_supplierForest_node_087368 else g32p_supplierForest_node_087403)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_087451 else g32p_supplierForest_node_087462) else (if i.val < 199 then g32p_supplierForest_node_087479 else g32p_supplierForest_node_087583))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_087652 else g32p_supplierForest_node_087670) else (if i.val < 203 then g32p_supplierForest_node_087672 else g32p_supplierForest_node_087715)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_087733 else g32p_supplierForest_node_087779) else (if i.val < 207 then g32p_supplierForest_node_087783 else g32p_supplierForest_node_087789)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_087821 else g32p_supplierForest_node_087823) else (if i.val < 211 then g32p_supplierForest_node_087838 else g32p_supplierForest_node_087881)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_087909 else g32p_supplierForest_node_087922) else (if i.val < 215 then g32p_supplierForest_node_087997 else g32p_supplierForest_node_088001))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_088005 else g32p_supplierForest_node_088058) else (if i.val < 219 then g32p_supplierForest_node_088068 else g32p_supplierForest_node_088115)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_088121 else g32p_supplierForest_node_088132) else (if i.val < 223 then g32p_supplierForest_node_088143 else g32p_supplierForest_node_088144))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_088184 else g32p_supplierForest_node_088234) else (if i.val < 227 then g32p_supplierForest_node_088237 else g32p_supplierForest_node_088239)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_088290 else g32p_supplierForest_node_088295) else (if i.val < 231 then g32p_supplierForest_node_088331 else g32p_supplierForest_node_088341))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_088345 else g32p_supplierForest_node_088367) else (if i.val < 235 then g32p_supplierForest_node_088419 else g32p_supplierForest_node_088421)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_088446 else g32p_supplierForest_node_088450) else (if i.val < 239 then g32p_supplierForest_node_088462 else g32p_supplierForest_node_088534)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_088535 else g32p_supplierForest_node_088577) else (if i.val < 243 then g32p_supplierForest_node_088582 else g32p_supplierForest_node_088583)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_088634 else g32p_supplierForest_node_088646) else (if i.val < 247 then g32p_supplierForest_node_088657 else g32p_supplierForest_node_088668))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_088675 else g32p_supplierForest_node_088676) else (if i.val < 251 then g32p_supplierForest_node_088701 else g32p_supplierForest_node_088786)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_088836 else g32p_supplierForest_node_088858) else (if i.val < 255 then g32p_supplierForest_node_088860 else g32p_supplierForest_node_088882))))))))

def g32p_supplierForest_classes_099 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 46 else 49) else (if i.val < 3 then 47 else 46)) else (if i.val < 6 then (if i.val < 5 then 10 else 49) else (if i.val < 7 then 47 else 10))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 48 else 49) else (if i.val < 11 then 50 else 25)) else (if i.val < 14 then (if i.val < 13 then 49 else 50) else (if i.val < 15 then 51 else 47)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 9 else 49) else (if i.val < 19 then 49 else 49)) else (if i.val < 22 then (if i.val < 21 then 84 else 12) else (if i.val < 23 then 49 else 80))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 46) else (if i.val < 27 then 49 else 47)) else (if i.val < 30 then (if i.val < 29 then 25 else 49) else (if i.val < 31 then 49 else 50))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 46 else 50) else (if i.val < 35 then 84 else 49)) else (if i.val < 38 then (if i.val < 37 then 46 else 48) else (if i.val < 39 then 55 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 50 else 53) else (if i.val < 43 then 49 else 46)) else (if i.val < 46 then (if i.val < 45 then 25 else 26) else (if i.val < 47 then 49 else 25)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 12 else 48) else (if i.val < 51 then 55 else 46)) else (if i.val < 54 then (if i.val < 53 then 46 else 84) else (if i.val < 55 then 80 else 50))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 53 else 47) else (if i.val < 59 then 47 else 49)) else (if i.val < 62 then (if i.val < 61 then 47 else 49) else (if i.val < 63 then 48 else 46)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 49) else (if i.val < 67 then 27 else 51)) else (if i.val < 70 then (if i.val < 69 then 50 else 53) else (if i.val < 71 then 12 else 12))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 25 else 49) else (if i.val < 75 then 49 else 46)) else (if i.val < 78 then (if i.val < 77 then 26 else 49) else (if i.val < 79 then 49 else 9)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 50 else 46) else (if i.val < 83 then 46 else 9)) else (if i.val < 86 then (if i.val < 85 then 49 else 46) else (if i.val < 87 then 49 else 49))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 49 else 46) else (if i.val < 91 then 84 else 46)) else (if i.val < 94 then (if i.val < 93 then 48 else 49) else (if i.val < 95 then 27 else 45))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 45 else 52) else (if i.val < 99 then 47 else 46)) else (if i.val < 102 then (if i.val < 101 then 47 else 46) else (if i.val < 103 then 46 else 46))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 25 else 55) else (if i.val < 107 then 46 else 46)) else (if i.val < 110 then (if i.val < 109 then 26 else 25) else (if i.val < 111 then 49 else 55)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 53 else 46) else (if i.val < 115 then 26 else 46)) else (if i.val < 118 then (if i.val < 117 then 46 else 46) else (if i.val < 119 then 46 else 46))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 49 else 49) else (if i.val < 123 then 49 else 49)) else (if i.val < 126 then (if i.val < 125 then 55 else 49) else (if i.val < 127 then 82 else 27))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 46) else (if i.val < 131 then 26 else 45)) else (if i.val < 134 then (if i.val < 133 then 46 else 46) else (if i.val < 135 then 49 else 49))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 55 else 45) else (if i.val < 139 then 47 else 46)) else (if i.val < 142 then (if i.val < 141 then 50 else 50) else (if i.val < 143 then 50 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 82 else 25) else (if i.val < 147 then 26 else 46)) else (if i.val < 150 then (if i.val < 149 then 45 else 82) else (if i.val < 151 then 47 else 80))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 49 else 54) else (if i.val < 155 then 48 else 49)) else (if i.val < 158 then (if i.val < 157 then 49 else 49) else (if i.val < 159 then 46 else 46))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 86 else 49) else (if i.val < 163 then 50 else 46)) else (if i.val < 166 then (if i.val < 165 then 84 else 47) else (if i.val < 167 then 53 else 49))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 47 else 54) else (if i.val < 171 then 50 else 50)) else (if i.val < 174 then (if i.val < 173 then 55 else 49) else (if i.val < 175 then 49 else 46)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 46 else 50) else (if i.val < 179 then 52 else 52)) else (if i.val < 182 then (if i.val < 181 then 49 else 80) else (if i.val < 183 then 50 else 13))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 80 else 49) else (if i.val < 187 then 25 else 50)) else (if i.val < 190 then (if i.val < 189 then 86 else 53) else (if i.val < 191 then 49 else 56)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 47 else 45) else (if i.val < 195 then 46 else 56)) else (if i.val < 198 then (if i.val < 197 then 46 else 49) else (if i.val < 199 then 46 else 46))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 46 else 46) else (if i.val < 203 then 49 else 46)) else (if i.val < 206 then (if i.val < 205 then 52 else 46) else (if i.val < 207 then 49 else 46)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 55 else 49) else (if i.val < 211 then 49 else 86)) else (if i.val < 214 then (if i.val < 213 then 49 else 25) else (if i.val < 215 then 55 else 53))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 55 else 9) else (if i.val < 219 then 80 else 55)) else (if i.val < 222 then (if i.val < 221 then 46 else 46) else (if i.val < 223 then 46 else 46))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 54 else 46) else (if i.val < 227 then 49 else 49)) else (if i.val < 230 then (if i.val < 229 then 9 else 49) else (if i.val < 231 then 47 else 49))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 49 else 26) else (if i.val < 235 then 46 else 49)) else (if i.val < 238 then (if i.val < 237 then 46 else 84) else (if i.val < 239 then 45 else 46)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 53 else 45) else (if i.val < 243 then 50 else 54)) else (if i.val < 246 then (if i.val < 245 then 50 else 26) else (if i.val < 247 then 46 else 49))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 46) else (if i.val < 251 then 53 else 26)) else (if i.val < 254 then (if i.val < 253 then 86 else 26) else (if i.val < 255 then 12 else 48))))))))

theorem g32p_supplierForest_actual_099 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_099 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_099 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_083253
  · exact g32p_supplierForest_actual_083291
  · exact g32p_supplierForest_actual_083301
  · exact g32p_supplierForest_actual_083329
  · exact g32p_supplierForest_actual_083368
  · exact g32p_supplierForest_actual_083373
  · exact g32p_supplierForest_actual_083375
  · exact g32p_supplierForest_actual_083391
  · exact g32p_supplierForest_actual_083409
  · exact g32p_supplierForest_actual_083427
  · exact g32p_supplierForest_actual_083430
  · exact g32p_supplierForest_actual_083438
  · exact g32p_supplierForest_actual_083439
  · exact g32p_supplierForest_actual_083489
  · exact g32p_supplierForest_actual_083490
  · exact g32p_supplierForest_actual_083494
  · exact g32p_supplierForest_actual_083555
  · exact g32p_supplierForest_actual_083567
  · exact g32p_supplierForest_actual_083568
  · exact g32p_supplierForest_actual_083664
  · exact g32p_supplierForest_actual_083681
  · exact g32p_supplierForest_actual_083686
  · exact g32p_supplierForest_actual_083703
  · exact g32p_supplierForest_actual_083763
  · exact g32p_supplierForest_actual_083769
  · exact g32p_supplierForest_actual_083797
  · exact g32p_supplierForest_actual_083806
  · exact g32p_supplierForest_actual_083837
  · exact g32p_supplierForest_actual_083895
  · exact g32p_supplierForest_actual_083915
  · exact g32p_supplierForest_actual_083965
  · exact g32p_supplierForest_actual_084008
  · exact g32p_supplierForest_actual_084013
  · exact g32p_supplierForest_actual_084022
  · exact g32p_supplierForest_actual_084025
  · exact g32p_supplierForest_actual_084035
  · exact g32p_supplierForest_actual_084055
  · exact g32p_supplierForest_actual_084058
  · exact g32p_supplierForest_actual_084060
  · exact g32p_supplierForest_actual_084085
  · exact g32p_supplierForest_actual_084088
  · exact g32p_supplierForest_actual_084096
  · exact g32p_supplierForest_actual_084166
  · exact g32p_supplierForest_actual_084237
  · exact g32p_supplierForest_actual_084286
  · exact g32p_supplierForest_actual_084315
  · exact g32p_supplierForest_actual_084317
  · exact g32p_supplierForest_actual_084345
  · exact g32p_supplierForest_actual_084379
  · exact g32p_supplierForest_actual_084390
  · exact g32p_supplierForest_actual_084414
  · exact g32p_supplierForest_actual_084444
  · exact g32p_supplierForest_actual_084486
  · exact g32p_supplierForest_actual_084512
  · exact g32p_supplierForest_actual_084555
  · exact g32p_supplierForest_actual_084579
  · exact g32p_supplierForest_actual_084596
  · exact g32p_supplierForest_actual_084626
  · exact g32p_supplierForest_actual_084633
  · exact g32p_supplierForest_actual_084639
  · exact g32p_supplierForest_actual_084648
  · exact g32p_supplierForest_actual_084663
  · exact g32p_supplierForest_actual_084670
  · exact g32p_supplierForest_actual_084671
  · exact g32p_supplierForest_actual_084716
  · exact g32p_supplierForest_actual_084738
  · exact g32p_supplierForest_actual_084742
  · exact g32p_supplierForest_actual_084750
  · exact g32p_supplierForest_actual_084766
  · exact g32p_supplierForest_actual_084779
  · exact g32p_supplierForest_actual_084797
  · exact g32p_supplierForest_actual_084833
  · exact g32p_supplierForest_actual_084853
  · exact g32p_supplierForest_actual_084881
  · exact g32p_supplierForest_actual_084931
  · exact g32p_supplierForest_actual_084933
  · exact g32p_supplierForest_actual_084936
  · exact g32p_supplierForest_actual_084951
  · exact g32p_supplierForest_actual_084957
  · exact g32p_supplierForest_actual_084958
  · exact g32p_supplierForest_actual_084976
  · exact g32p_supplierForest_actual_085105
  · exact g32p_supplierForest_actual_085120
  · exact g32p_supplierForest_actual_085144
  · exact g32p_supplierForest_actual_085152
  · exact g32p_supplierForest_actual_085162
  · exact g32p_supplierForest_actual_085202
  · exact g32p_supplierForest_actual_085209
  · exact g32p_supplierForest_actual_085232
  · exact g32p_supplierForest_actual_085243
  · exact g32p_supplierForest_actual_085250
  · exact g32p_supplierForest_actual_085286
  · exact g32p_supplierForest_actual_085320
  · exact g32p_supplierForest_actual_085361
  · exact g32p_supplierForest_actual_085377
  · exact g32p_supplierForest_actual_085416
  · exact g32p_supplierForest_actual_085433
  · exact g32p_supplierForest_actual_085435
  · exact g32p_supplierForest_actual_085444
  · exact g32p_supplierForest_actual_085447
  · exact g32p_supplierForest_actual_085449
  · exact g32p_supplierForest_actual_085454
  · exact g32p_supplierForest_actual_085455
  · exact g32p_supplierForest_actual_085458
  · exact g32p_supplierForest_actual_085491
  · exact g32p_supplierForest_actual_085494
  · exact g32p_supplierForest_actual_085534
  · exact g32p_supplierForest_actual_085557
  · exact g32p_supplierForest_actual_085559
  · exact g32p_supplierForest_actual_085629
  · exact g32p_supplierForest_actual_085663
  · exact g32p_supplierForest_actual_085666
  · exact g32p_supplierForest_actual_085683
  · exact g32p_supplierForest_actual_085687
  · exact g32p_supplierForest_actual_085726
  · exact g32p_supplierForest_actual_085740
  · exact g32p_supplierForest_actual_085757
  · exact g32p_supplierForest_actual_085764
  · exact g32p_supplierForest_actual_085783
  · exact g32p_supplierForest_actual_085832
  · exact g32p_supplierForest_actual_085847
  · exact g32p_supplierForest_actual_085870
  · exact g32p_supplierForest_actual_085879
  · exact g32p_supplierForest_actual_085885
  · exact g32p_supplierForest_actual_085902
  · exact g32p_supplierForest_actual_085952
  · exact g32p_supplierForest_actual_086022
  · exact g32p_supplierForest_actual_086060
  · exact g32p_supplierForest_actual_086068
  · exact g32p_supplierForest_actual_086085
  · exact g32p_supplierForest_actual_086088
  · exact g32p_supplierForest_actual_086128
  · exact g32p_supplierForest_actual_086138
  · exact g32p_supplierForest_actual_086167
  · exact g32p_supplierForest_actual_086204
  · exact g32p_supplierForest_actual_086217
  · exact g32p_supplierForest_actual_086230
  · exact g32p_supplierForest_actual_086270
  · exact g32p_supplierForest_actual_086300
  · exact g32p_supplierForest_actual_086324
  · exact g32p_supplierForest_actual_086365
  · exact g32p_supplierForest_actual_086382
  · exact g32p_supplierForest_actual_086387
  · exact g32p_supplierForest_actual_086388
  · exact g32p_supplierForest_actual_086430
  · exact g32p_supplierForest_actual_086433
  · exact g32p_supplierForest_actual_086457
  · exact g32p_supplierForest_actual_086465
  · exact g32p_supplierForest_actual_086491
  · exact g32p_supplierForest_actual_086526
  · exact g32p_supplierForest_actual_086538
  · exact g32p_supplierForest_actual_086544
  · exact g32p_supplierForest_actual_086591
  · exact g32p_supplierForest_actual_086617
  · exact g32p_supplierForest_actual_086618
  · exact g32p_supplierForest_actual_086662
  · exact g32p_supplierForest_actual_086686
  · exact g32p_supplierForest_actual_086698
  · exact g32p_supplierForest_actual_086727
  · exact g32p_supplierForest_actual_086742
  · exact g32p_supplierForest_actual_086801
  · exact g32p_supplierForest_actual_086803
  · exact g32p_supplierForest_actual_086809
  · exact g32p_supplierForest_actual_086832
  · exact g32p_supplierForest_actual_086839
  · exact g32p_supplierForest_actual_086840
  · exact g32p_supplierForest_actual_086859
  · exact g32p_supplierForest_actual_086865
  · exact g32p_supplierForest_actual_086877
  · exact g32p_supplierForest_actual_086885
  · exact g32p_supplierForest_actual_086892
  · exact g32p_supplierForest_actual_086905
  · exact g32p_supplierForest_actual_086922
  · exact g32p_supplierForest_actual_086927
  · exact g32p_supplierForest_actual_086936
  · exact g32p_supplierForest_actual_086958
  · exact g32p_supplierForest_actual_086961
  · exact g32p_supplierForest_actual_086963
  · exact g32p_supplierForest_actual_087021
  · exact g32p_supplierForest_actual_087040
  · exact g32p_supplierForest_actual_087049
  · exact g32p_supplierForest_actual_087064
  · exact g32p_supplierForest_actual_087088
  · exact g32p_supplierForest_actual_087182
  · exact g32p_supplierForest_actual_087192
  · exact g32p_supplierForest_actual_087194
  · exact g32p_supplierForest_actual_087208
  · exact g32p_supplierForest_actual_087225
  · exact g32p_supplierForest_actual_087282
  · exact g32p_supplierForest_actual_087297
  · exact g32p_supplierForest_actual_087302
  · exact g32p_supplierForest_actual_087321
  · exact g32p_supplierForest_actual_087327
  · exact g32p_supplierForest_actual_087364
  · exact g32p_supplierForest_actual_087368
  · exact g32p_supplierForest_actual_087403
  · exact g32p_supplierForest_actual_087451
  · exact g32p_supplierForest_actual_087462
  · exact g32p_supplierForest_actual_087479
  · exact g32p_supplierForest_actual_087583
  · exact g32p_supplierForest_actual_087652
  · exact g32p_supplierForest_actual_087670
  · exact g32p_supplierForest_actual_087672
  · exact g32p_supplierForest_actual_087715
  · exact g32p_supplierForest_actual_087733
  · exact g32p_supplierForest_actual_087779
  · exact g32p_supplierForest_actual_087783
  · exact g32p_supplierForest_actual_087789
  · exact g32p_supplierForest_actual_087821
  · exact g32p_supplierForest_actual_087823
  · exact g32p_supplierForest_actual_087838
  · exact g32p_supplierForest_actual_087881
  · exact g32p_supplierForest_actual_087909
  · exact g32p_supplierForest_actual_087922
  · exact g32p_supplierForest_actual_087997
  · exact g32p_supplierForest_actual_088001
  · exact g32p_supplierForest_actual_088005
  · exact g32p_supplierForest_actual_088058
  · exact g32p_supplierForest_actual_088068
  · exact g32p_supplierForest_actual_088115
  · exact g32p_supplierForest_actual_088121
  · exact g32p_supplierForest_actual_088132
  · exact g32p_supplierForest_actual_088143
  · exact g32p_supplierForest_actual_088144
  · exact g32p_supplierForest_actual_088184
  · exact g32p_supplierForest_actual_088234
  · exact g32p_supplierForest_actual_088237
  · exact g32p_supplierForest_actual_088239
  · exact g32p_supplierForest_actual_088290
  · exact g32p_supplierForest_actual_088295
  · exact g32p_supplierForest_actual_088331
  · exact g32p_supplierForest_actual_088341
  · exact g32p_supplierForest_actual_088345
  · exact g32p_supplierForest_actual_088367
  · exact g32p_supplierForest_actual_088419
  · exact g32p_supplierForest_actual_088421
  · exact g32p_supplierForest_actual_088446
  · exact g32p_supplierForest_actual_088450
  · exact g32p_supplierForest_actual_088462
  · exact g32p_supplierForest_actual_088534
  · exact g32p_supplierForest_actual_088535
  · exact g32p_supplierForest_actual_088577
  · exact g32p_supplierForest_actual_088582
  · exact g32p_supplierForest_actual_088583
  · exact g32p_supplierForest_actual_088634
  · exact g32p_supplierForest_actual_088646
  · exact g32p_supplierForest_actual_088657
  · exact g32p_supplierForest_actual_088668
  · exact g32p_supplierForest_actual_088675
  · exact g32p_supplierForest_actual_088676
  · exact g32p_supplierForest_actual_088701
  · exact g32p_supplierForest_actual_088786
  · exact g32p_supplierForest_actual_088836
  · exact g32p_supplierForest_actual_088858
  · exact g32p_supplierForest_actual_088860
  · exact g32p_supplierForest_actual_088882

def g32p_supplierForest_nodes_100 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_088909 else g32p_supplierForest_node_088922) else (if i.val < 3 then g32p_supplierForest_node_088959 else g32p_supplierForest_node_088974)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_088978 else g32p_supplierForest_node_089046) else (if i.val < 7 then g32p_supplierForest_node_089054 else g32p_supplierForest_node_089056))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_089096 else g32p_supplierForest_node_089112) else (if i.val < 11 then g32p_supplierForest_node_089133 else g32p_supplierForest_node_089142)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_089199 else g32p_supplierForest_node_089206) else (if i.val < 15 then g32p_supplierForest_node_089241 else g32p_supplierForest_node_089254)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_089318 else g32p_supplierForest_node_089336) else (if i.val < 19 then g32p_supplierForest_node_089379 else g32p_supplierForest_node_089392)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_089399 else g32p_supplierForest_node_089422) else (if i.val < 23 then g32p_supplierForest_node_089450 else g32p_supplierForest_node_089474))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_089502 else g32p_supplierForest_node_089516) else (if i.val < 27 then g32p_supplierForest_node_089577 else g32p_supplierForest_node_089607)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_089642 else g32p_supplierForest_node_089664) else (if i.val < 31 then g32p_supplierForest_node_089714 else g32p_supplierForest_node_089718))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_089762 else g32p_supplierForest_node_089774) else (if i.val < 35 then g32p_supplierForest_node_089780 else g32p_supplierForest_node_089781)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_089795 else g32p_supplierForest_node_089855) else (if i.val < 39 then g32p_supplierForest_node_089933 else g32p_supplierForest_node_089972))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_089990 else g32p_supplierForest_node_090000) else (if i.val < 43 then g32p_supplierForest_node_090021 else g32p_supplierForest_node_090043)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_090067 else g32p_supplierForest_node_090090) else (if i.val < 47 then g32p_supplierForest_node_090097 else g32p_supplierForest_node_090110)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_090123 else g32p_supplierForest_node_090127) else (if i.val < 51 then g32p_supplierForest_node_090178 else g32p_supplierForest_node_090185)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_090187 else g32p_supplierForest_node_090217) else (if i.val < 55 then g32p_supplierForest_node_090231 else g32p_supplierForest_node_090234))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_090278 else g32p_supplierForest_node_090279) else (if i.val < 59 then g32p_supplierForest_node_090297 else g32p_supplierForest_node_090319)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_090397 else g32p_supplierForest_node_090401) else (if i.val < 63 then g32p_supplierForest_node_090427 else g32p_supplierForest_node_090443)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_090447 else g32p_supplierForest_node_090452) else (if i.val < 67 then g32p_supplierForest_node_090465 else g32p_supplierForest_node_090488)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_090508 else g32p_supplierForest_node_090521) else (if i.val < 71 then g32p_supplierForest_node_090573 else g32p_supplierForest_node_090585))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_090600 else g32p_supplierForest_node_090660) else (if i.val < 75 then g32p_supplierForest_node_090677 else g32p_supplierForest_node_090716)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_090751 else g32p_supplierForest_node_090781) else (if i.val < 79 then g32p_supplierForest_node_090864 else g32p_supplierForest_node_090887)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_090914 else g32p_supplierForest_node_090941) else (if i.val < 83 then g32p_supplierForest_node_090952 else g32p_supplierForest_node_090964)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_090996 else g32p_supplierForest_node_091018) else (if i.val < 87 then g32p_supplierForest_node_091138 else g32p_supplierForest_node_091144))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_091156 else g32p_supplierForest_node_091180) else (if i.val < 91 then g32p_supplierForest_node_091186 else g32p_supplierForest_node_091209)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_091211 else g32p_supplierForest_node_091281) else (if i.val < 95 then g32p_supplierForest_node_091287 else g32p_supplierForest_node_091318))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_091319 else g32p_supplierForest_node_091328) else (if i.val < 99 then g32p_supplierForest_node_091340 else g32p_supplierForest_node_091355)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_091363 else g32p_supplierForest_node_091368) else (if i.val < 103 then g32p_supplierForest_node_091381 else g32p_supplierForest_node_091397))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_091422 else g32p_supplierForest_node_091440) else (if i.val < 107 then g32p_supplierForest_node_091447 else g32p_supplierForest_node_091455)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_091468 else g32p_supplierForest_node_091477) else (if i.val < 111 then g32p_supplierForest_node_091494 else g32p_supplierForest_node_091504)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_091512 else g32p_supplierForest_node_091516) else (if i.val < 115 then g32p_supplierForest_node_091521 else g32p_supplierForest_node_091528)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_091540 else g32p_supplierForest_node_091548) else (if i.val < 119 then g32p_supplierForest_node_091653 else g32p_supplierForest_node_091663))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_091674 else g32p_supplierForest_node_091677) else (if i.val < 123 then g32p_supplierForest_node_091710 else g32p_supplierForest_node_091728)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_091732 else g32p_supplierForest_node_091739) else (if i.val < 127 then g32p_supplierForest_node_091748 else g32p_supplierForest_node_091833))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_091837 else g32p_supplierForest_node_091844) else (if i.val < 131 then g32p_supplierForest_node_091853 else g32p_supplierForest_node_091855)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_091868 else g32p_supplierForest_node_091899) else (if i.val < 135 then g32p_supplierForest_node_091911 else g32p_supplierForest_node_091940))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_091945 else g32p_supplierForest_node_091965) else (if i.val < 139 then g32p_supplierForest_node_091985 else g32p_supplierForest_node_092015)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_092020 else g32p_supplierForest_node_092024) else (if i.val < 143 then g32p_supplierForest_node_092027 else g32p_supplierForest_node_092057)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_092095 else g32p_supplierForest_node_092113) else (if i.val < 147 then g32p_supplierForest_node_092116 else g32p_supplierForest_node_092121)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_092131 else g32p_supplierForest_node_092133) else (if i.val < 151 then g32p_supplierForest_node_092166 else g32p_supplierForest_node_092177))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_092192 else g32p_supplierForest_node_092197) else (if i.val < 155 then g32p_supplierForest_node_092206 else g32p_supplierForest_node_092213)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_092216 else g32p_supplierForest_node_092225) else (if i.val < 159 then g32p_supplierForest_node_092228 else g32p_supplierForest_node_092246))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_092268 else g32p_supplierForest_node_092304) else (if i.val < 163 then g32p_supplierForest_node_092309 else g32p_supplierForest_node_092342)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_092356 else g32p_supplierForest_node_092358) else (if i.val < 167 then g32p_supplierForest_node_092388 else g32p_supplierForest_node_092392))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_092436 else g32p_supplierForest_node_092466) else (if i.val < 171 then g32p_supplierForest_node_092522 else g32p_supplierForest_node_092585)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_092594 else g32p_supplierForest_node_092612) else (if i.val < 175 then g32p_supplierForest_node_092614 else g32p_supplierForest_node_092635)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_092637 else g32p_supplierForest_node_092654) else (if i.val < 179 then g32p_supplierForest_node_092687 else g32p_supplierForest_node_092724)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_092734 else g32p_supplierForest_node_092801) else (if i.val < 183 then g32p_supplierForest_node_092803 else g32p_supplierForest_node_092844))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_092856 else g32p_supplierForest_node_092868) else (if i.val < 187 then g32p_supplierForest_node_092900 else g32p_supplierForest_node_092903)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_092940 else g32p_supplierForest_node_092970) else (if i.val < 191 then g32p_supplierForest_node_092991 else g32p_supplierForest_node_093003)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_093023 else g32p_supplierForest_node_093059) else (if i.val < 195 then g32p_supplierForest_node_093090 else g32p_supplierForest_node_093100)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_093111 else g32p_supplierForest_node_093127) else (if i.val < 199 then g32p_supplierForest_node_093155 else g32p_supplierForest_node_093182))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_093210 else g32p_supplierForest_node_093213) else (if i.val < 203 then g32p_supplierForest_node_093228 else g32p_supplierForest_node_093235)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_093257 else g32p_supplierForest_node_093260) else (if i.val < 207 then g32p_supplierForest_node_093267 else g32p_supplierForest_node_093271)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_093285 else g32p_supplierForest_node_093290) else (if i.val < 211 then g32p_supplierForest_node_093295 else g32p_supplierForest_node_093338)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_093357 else g32p_supplierForest_node_093378) else (if i.val < 215 then g32p_supplierForest_node_093380 else g32p_supplierForest_node_093382))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_093390 else g32p_supplierForest_node_093395) else (if i.val < 219 then g32p_supplierForest_node_093456 else g32p_supplierForest_node_093465)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_093483 else g32p_supplierForest_node_093497) else (if i.val < 223 then g32p_supplierForest_node_093538 else g32p_supplierForest_node_093571))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_093592 else g32p_supplierForest_node_093627) else (if i.val < 227 then g32p_supplierForest_node_093652 else g32p_supplierForest_node_093658)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_093660 else g32p_supplierForest_node_093685) else (if i.val < 231 then g32p_supplierForest_node_093686 else g32p_supplierForest_node_093720))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_093723 else g32p_supplierForest_node_093741) else (if i.val < 235 then g32p_supplierForest_node_093745 else g32p_supplierForest_node_093792)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_093801 else g32p_supplierForest_node_093805) else (if i.val < 239 then g32p_supplierForest_node_093814 else g32p_supplierForest_node_093815)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_093820 else g32p_supplierForest_node_093919) else (if i.val < 243 then g32p_supplierForest_node_093933 else g32p_supplierForest_node_093935)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_093978 else g32p_supplierForest_node_093999) else (if i.val < 247 then g32p_supplierForest_node_094031 else g32p_supplierForest_node_094037))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_094043 else g32p_supplierForest_node_094081) else (if i.val < 251 then g32p_supplierForest_node_094099 else g32p_supplierForest_node_094104)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_094119 else g32p_supplierForest_node_094145) else (if i.val < 255 then g32p_supplierForest_node_094164 else g32p_supplierForest_node_094187))))))))

def g32p_supplierForest_classes_100 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 49 else 46) else (if i.val < 3 then 48 else 80)) else (if i.val < 6 then (if i.val < 5 then 46 else 53) else (if i.val < 7 then 45 else 46))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 84 else 80) else (if i.val < 11 then 46 else 55)) else (if i.val < 14 then (if i.val < 13 then 46 else 49) else (if i.val < 15 then 26 else 47)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 46 else 53) else (if i.val < 19 then 48 else 49)) else (if i.val < 22 then (if i.val < 21 then 49 else 49) else (if i.val < 23 then 50 else 49))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 55 else 49) else (if i.val < 27 then 45 else 46)) else (if i.val < 30 then (if i.val < 29 then 25 else 49) else (if i.val < 31 then 46 else 47))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 86 else 80) else (if i.val < 35 then 49 else 47)) else (if i.val < 38 then (if i.val < 37 then 49 else 53) else (if i.val < 39 then 46 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 49 else 26) else (if i.val < 43 then 46 else 26)) else (if i.val < 46 then (if i.val < 45 then 84 else 52) else (if i.val < 47 then 49 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 46 else 25) else (if i.val < 51 then 49 else 49)) else (if i.val < 54 then (if i.val < 53 then 49 else 13) else (if i.val < 55 then 83 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 50 else 47) else (if i.val < 59 then 46 else 49)) else (if i.val < 62 then (if i.val < 61 then 53 else 46) else (if i.val < 63 then 46 else 47)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 55) else (if i.val < 67 then 10 else 27)) else (if i.val < 70 then (if i.val < 69 then 46 else 80) else (if i.val < 71 then 46 else 84))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 54 else 46) else (if i.val < 75 then 49 else 55)) else (if i.val < 78 then (if i.val < 77 then 47 else 25) else (if i.val < 79 then 55 else 46)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 53 else 47) else (if i.val < 83 then 49 else 86)) else (if i.val < 86 then (if i.val < 85 then 26 else 49) else (if i.val < 87 then 49 else 49))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 49 else 46) else (if i.val < 91 then 26 else 49)) else (if i.val < 94 then (if i.val < 93 then 46 else 49) else (if i.val < 95 then 25 else 55))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 25 else 55) else (if i.val < 99 then 46 else 9)) else (if i.val < 102 then (if i.val < 101 then 47 else 10) else (if i.val < 103 then 50 else 47))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 80 else 49) else (if i.val < 107 then 49 else 25)) else (if i.val < 110 then (if i.val < 109 then 47 else 86) else (if i.val < 111 then 49 else 49)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 49 else 46) else (if i.val < 115 then 46 else 26)) else (if i.val < 118 then (if i.val < 117 then 46 else 49) else (if i.val < 119 then 25 else 53))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 46 else 50) else (if i.val < 123 then 80 else 26)) else (if i.val < 126 then (if i.val < 125 then 49 else 45) else (if i.val < 127 then 50 else 49))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 49 else 46) else (if i.val < 131 then 80 else 49)) else (if i.val < 134 then (if i.val < 133 then 49 else 50) else (if i.val < 135 then 46 else 85))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 49 else 53) else (if i.val < 139 then 86 else 13)) else (if i.val < 142 then (if i.val < 141 then 52 else 54) else (if i.val < 143 then 46 else 25)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 47 else 49) else (if i.val < 147 then 47 else 46)) else (if i.val < 150 then (if i.val < 149 then 49 else 85) else (if i.val < 151 then 46 else 26))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 50 else 50) else (if i.val < 155 then 49 else 54)) else (if i.val < 158 then (if i.val < 157 then 25 else 49) else (if i.val < 159 then 46 else 46))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 49 else 83) else (if i.val < 163 then 50 else 54)) else (if i.val < 166 then (if i.val < 165 then 46 else 26) else (if i.val < 167 then 83 else 55))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 81) else (if i.val < 171 then 46 else 46)) else (if i.val < 174 then (if i.val < 173 then 46 else 46) else (if i.val < 175 then 46 else 85)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 50 else 46) else (if i.val < 179 then 27 else 47)) else (if i.val < 182 then (if i.val < 181 then 49 else 50) else (if i.val < 183 then 50 else 46))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 26 else 47) else (if i.val < 187 then 46 else 26)) else (if i.val < 190 then (if i.val < 189 then 47 else 46) else (if i.val < 191 then 46 else 47)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 46 else 84) else (if i.val < 195 then 46 else 45)) else (if i.val < 198 then (if i.val < 197 then 49 else 13) else (if i.val < 199 then 55 else 50))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 26 else 46) else (if i.val < 203 then 46 else 46)) else (if i.val < 206 then (if i.val < 205 then 46 else 49) else (if i.val < 207 then 11 else 46)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 55 else 86) else (if i.val < 211 then 47 else 26)) else (if i.val < 214 then (if i.val < 213 then 49 else 25) else (if i.val < 215 then 50 else 45))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 46 else 46) else (if i.val < 219 then 84 else 46)) else (if i.val < 222 then (if i.val < 221 then 49 else 49) else (if i.val < 223 then 27 else 49))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 45 else 80) else (if i.val < 227 then 84 else 45)) else (if i.val < 230 then (if i.val < 229 then 49 else 46) else (if i.val < 231 then 83 else 49))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 49 else 49) else (if i.val < 235 then 53 else 46)) else (if i.val < 238 then (if i.val < 237 then 46 else 49) else (if i.val < 239 then 46 else 25)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 25) else (if i.val < 243 then 12 else 46)) else (if i.val < 246 then (if i.val < 245 then 47 else 13) else (if i.val < 247 then 46 else 26))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 25 else 46) else (if i.val < 251 then 13 else 45)) else (if i.val < 254 then (if i.val < 253 then 26 else 49) else (if i.val < 255 then 86 else 46))))))))

theorem g32p_supplierForest_actual_100 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_100 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_100 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_088909
  · exact g32p_supplierForest_actual_088922
  · exact g32p_supplierForest_actual_088959
  · exact g32p_supplierForest_actual_088974
  · exact g32p_supplierForest_actual_088978
  · exact g32p_supplierForest_actual_089046
  · exact g32p_supplierForest_actual_089054
  · exact g32p_supplierForest_actual_089056
  · exact g32p_supplierForest_actual_089096
  · exact g32p_supplierForest_actual_089112
  · exact g32p_supplierForest_actual_089133
  · exact g32p_supplierForest_actual_089142
  · exact g32p_supplierForest_actual_089199
  · exact g32p_supplierForest_actual_089206
  · exact g32p_supplierForest_actual_089241
  · exact g32p_supplierForest_actual_089254
  · exact g32p_supplierForest_actual_089318
  · exact g32p_supplierForest_actual_089336
  · exact g32p_supplierForest_actual_089379
  · exact g32p_supplierForest_actual_089392
  · exact g32p_supplierForest_actual_089399
  · exact g32p_supplierForest_actual_089422
  · exact g32p_supplierForest_actual_089450
  · exact g32p_supplierForest_actual_089474
  · exact g32p_supplierForest_actual_089502
  · exact g32p_supplierForest_actual_089516
  · exact g32p_supplierForest_actual_089577
  · exact g32p_supplierForest_actual_089607
  · exact g32p_supplierForest_actual_089642
  · exact g32p_supplierForest_actual_089664
  · exact g32p_supplierForest_actual_089714
  · exact g32p_supplierForest_actual_089718
  · exact g32p_supplierForest_actual_089762
  · exact g32p_supplierForest_actual_089774
  · exact g32p_supplierForest_actual_089780
  · exact g32p_supplierForest_actual_089781
  · exact g32p_supplierForest_actual_089795
  · exact g32p_supplierForest_actual_089855
  · exact g32p_supplierForest_actual_089933
  · exact g32p_supplierForest_actual_089972
  · exact g32p_supplierForest_actual_089990
  · exact g32p_supplierForest_actual_090000
  · exact g32p_supplierForest_actual_090021
  · exact g32p_supplierForest_actual_090043
  · exact g32p_supplierForest_actual_090067
  · exact g32p_supplierForest_actual_090090
  · exact g32p_supplierForest_actual_090097
  · exact g32p_supplierForest_actual_090110
  · exact g32p_supplierForest_actual_090123
  · exact g32p_supplierForest_actual_090127
  · exact g32p_supplierForest_actual_090178
  · exact g32p_supplierForest_actual_090185
  · exact g32p_supplierForest_actual_090187
  · exact g32p_supplierForest_actual_090217
  · exact g32p_supplierForest_actual_090231
  · exact g32p_supplierForest_actual_090234
  · exact g32p_supplierForest_actual_090278
  · exact g32p_supplierForest_actual_090279
  · exact g32p_supplierForest_actual_090297
  · exact g32p_supplierForest_actual_090319
  · exact g32p_supplierForest_actual_090397
  · exact g32p_supplierForest_actual_090401
  · exact g32p_supplierForest_actual_090427
  · exact g32p_supplierForest_actual_090443
  · exact g32p_supplierForest_actual_090447
  · exact g32p_supplierForest_actual_090452
  · exact g32p_supplierForest_actual_090465
  · exact g32p_supplierForest_actual_090488
  · exact g32p_supplierForest_actual_090508
  · exact g32p_supplierForest_actual_090521
  · exact g32p_supplierForest_actual_090573
  · exact g32p_supplierForest_actual_090585
  · exact g32p_supplierForest_actual_090600
  · exact g32p_supplierForest_actual_090660
  · exact g32p_supplierForest_actual_090677
  · exact g32p_supplierForest_actual_090716
  · exact g32p_supplierForest_actual_090751
  · exact g32p_supplierForest_actual_090781
  · exact g32p_supplierForest_actual_090864
  · exact g32p_supplierForest_actual_090887
  · exact g32p_supplierForest_actual_090914
  · exact g32p_supplierForest_actual_090941
  · exact g32p_supplierForest_actual_090952
  · exact g32p_supplierForest_actual_090964
  · exact g32p_supplierForest_actual_090996
  · exact g32p_supplierForest_actual_091018
  · exact g32p_supplierForest_actual_091138
  · exact g32p_supplierForest_actual_091144
  · exact g32p_supplierForest_actual_091156
  · exact g32p_supplierForest_actual_091180
  · exact g32p_supplierForest_actual_091186
  · exact g32p_supplierForest_actual_091209
  · exact g32p_supplierForest_actual_091211
  · exact g32p_supplierForest_actual_091281
  · exact g32p_supplierForest_actual_091287
  · exact g32p_supplierForest_actual_091318
  · exact g32p_supplierForest_actual_091319
  · exact g32p_supplierForest_actual_091328
  · exact g32p_supplierForest_actual_091340
  · exact g32p_supplierForest_actual_091355
  · exact g32p_supplierForest_actual_091363
  · exact g32p_supplierForest_actual_091368
  · exact g32p_supplierForest_actual_091381
  · exact g32p_supplierForest_actual_091397
  · exact g32p_supplierForest_actual_091422
  · exact g32p_supplierForest_actual_091440
  · exact g32p_supplierForest_actual_091447
  · exact g32p_supplierForest_actual_091455
  · exact g32p_supplierForest_actual_091468
  · exact g32p_supplierForest_actual_091477
  · exact g32p_supplierForest_actual_091494
  · exact g32p_supplierForest_actual_091504
  · exact g32p_supplierForest_actual_091512
  · exact g32p_supplierForest_actual_091516
  · exact g32p_supplierForest_actual_091521
  · exact g32p_supplierForest_actual_091528
  · exact g32p_supplierForest_actual_091540
  · exact g32p_supplierForest_actual_091548
  · exact g32p_supplierForest_actual_091653
  · exact g32p_supplierForest_actual_091663
  · exact g32p_supplierForest_actual_091674
  · exact g32p_supplierForest_actual_091677
  · exact g32p_supplierForest_actual_091710
  · exact g32p_supplierForest_actual_091728
  · exact g32p_supplierForest_actual_091732
  · exact g32p_supplierForest_actual_091739
  · exact g32p_supplierForest_actual_091748
  · exact g32p_supplierForest_actual_091833
  · exact g32p_supplierForest_actual_091837
  · exact g32p_supplierForest_actual_091844
  · exact g32p_supplierForest_actual_091853
  · exact g32p_supplierForest_actual_091855
  · exact g32p_supplierForest_actual_091868
  · exact g32p_supplierForest_actual_091899
  · exact g32p_supplierForest_actual_091911
  · exact g32p_supplierForest_actual_091940
  · exact g32p_supplierForest_actual_091945
  · exact g32p_supplierForest_actual_091965
  · exact g32p_supplierForest_actual_091985
  · exact g32p_supplierForest_actual_092015
  · exact g32p_supplierForest_actual_092020
  · exact g32p_supplierForest_actual_092024
  · exact g32p_supplierForest_actual_092027
  · exact g32p_supplierForest_actual_092057
  · exact g32p_supplierForest_actual_092095
  · exact g32p_supplierForest_actual_092113
  · exact g32p_supplierForest_actual_092116
  · exact g32p_supplierForest_actual_092121
  · exact g32p_supplierForest_actual_092131
  · exact g32p_supplierForest_actual_092133
  · exact g32p_supplierForest_actual_092166
  · exact g32p_supplierForest_actual_092177
  · exact g32p_supplierForest_actual_092192
  · exact g32p_supplierForest_actual_092197
  · exact g32p_supplierForest_actual_092206
  · exact g32p_supplierForest_actual_092213
  · exact g32p_supplierForest_actual_092216
  · exact g32p_supplierForest_actual_092225
  · exact g32p_supplierForest_actual_092228
  · exact g32p_supplierForest_actual_092246
  · exact g32p_supplierForest_actual_092268
  · exact g32p_supplierForest_actual_092304
  · exact g32p_supplierForest_actual_092309
  · exact g32p_supplierForest_actual_092342
  · exact g32p_supplierForest_actual_092356
  · exact g32p_supplierForest_actual_092358
  · exact g32p_supplierForest_actual_092388
  · exact g32p_supplierForest_actual_092392
  · exact g32p_supplierForest_actual_092436
  · exact g32p_supplierForest_actual_092466
  · exact g32p_supplierForest_actual_092522
  · exact g32p_supplierForest_actual_092585
  · exact g32p_supplierForest_actual_092594
  · exact g32p_supplierForest_actual_092612
  · exact g32p_supplierForest_actual_092614
  · exact g32p_supplierForest_actual_092635
  · exact g32p_supplierForest_actual_092637
  · exact g32p_supplierForest_actual_092654
  · exact g32p_supplierForest_actual_092687
  · exact g32p_supplierForest_actual_092724
  · exact g32p_supplierForest_actual_092734
  · exact g32p_supplierForest_actual_092801
  · exact g32p_supplierForest_actual_092803
  · exact g32p_supplierForest_actual_092844
  · exact g32p_supplierForest_actual_092856
  · exact g32p_supplierForest_actual_092868
  · exact g32p_supplierForest_actual_092900
  · exact g32p_supplierForest_actual_092903
  · exact g32p_supplierForest_actual_092940
  · exact g32p_supplierForest_actual_092970
  · exact g32p_supplierForest_actual_092991
  · exact g32p_supplierForest_actual_093003
  · exact g32p_supplierForest_actual_093023
  · exact g32p_supplierForest_actual_093059
  · exact g32p_supplierForest_actual_093090
  · exact g32p_supplierForest_actual_093100
  · exact g32p_supplierForest_actual_093111
  · exact g32p_supplierForest_actual_093127
  · exact g32p_supplierForest_actual_093155
  · exact g32p_supplierForest_actual_093182
  · exact g32p_supplierForest_actual_093210
  · exact g32p_supplierForest_actual_093213
  · exact g32p_supplierForest_actual_093228
  · exact g32p_supplierForest_actual_093235
  · exact g32p_supplierForest_actual_093257
  · exact g32p_supplierForest_actual_093260
  · exact g32p_supplierForest_actual_093267
  · exact g32p_supplierForest_actual_093271
  · exact g32p_supplierForest_actual_093285
  · exact g32p_supplierForest_actual_093290
  · exact g32p_supplierForest_actual_093295
  · exact g32p_supplierForest_actual_093338
  · exact g32p_supplierForest_actual_093357
  · exact g32p_supplierForest_actual_093378
  · exact g32p_supplierForest_actual_093380
  · exact g32p_supplierForest_actual_093382
  · exact g32p_supplierForest_actual_093390
  · exact g32p_supplierForest_actual_093395
  · exact g32p_supplierForest_actual_093456
  · exact g32p_supplierForest_actual_093465
  · exact g32p_supplierForest_actual_093483
  · exact g32p_supplierForest_actual_093497
  · exact g32p_supplierForest_actual_093538
  · exact g32p_supplierForest_actual_093571
  · exact g32p_supplierForest_actual_093592
  · exact g32p_supplierForest_actual_093627
  · exact g32p_supplierForest_actual_093652
  · exact g32p_supplierForest_actual_093658
  · exact g32p_supplierForest_actual_093660
  · exact g32p_supplierForest_actual_093685
  · exact g32p_supplierForest_actual_093686
  · exact g32p_supplierForest_actual_093720
  · exact g32p_supplierForest_actual_093723
  · exact g32p_supplierForest_actual_093741
  · exact g32p_supplierForest_actual_093745
  · exact g32p_supplierForest_actual_093792
  · exact g32p_supplierForest_actual_093801
  · exact g32p_supplierForest_actual_093805
  · exact g32p_supplierForest_actual_093814
  · exact g32p_supplierForest_actual_093815
  · exact g32p_supplierForest_actual_093820
  · exact g32p_supplierForest_actual_093919
  · exact g32p_supplierForest_actual_093933
  · exact g32p_supplierForest_actual_093935
  · exact g32p_supplierForest_actual_093978
  · exact g32p_supplierForest_actual_093999
  · exact g32p_supplierForest_actual_094031
  · exact g32p_supplierForest_actual_094037
  · exact g32p_supplierForest_actual_094043
  · exact g32p_supplierForest_actual_094081
  · exact g32p_supplierForest_actual_094099
  · exact g32p_supplierForest_actual_094104
  · exact g32p_supplierForest_actual_094119
  · exact g32p_supplierForest_actual_094145
  · exact g32p_supplierForest_actual_094164
  · exact g32p_supplierForest_actual_094187

def g32p_supplierForest_nodes_101 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_094191 else g32p_supplierForest_node_094204) else (if i.val < 3 then g32p_supplierForest_node_094232 else g32p_supplierForest_node_094243)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_094287 else g32p_supplierForest_node_094295) else (if i.val < 7 then g32p_supplierForest_node_094302 else g32p_supplierForest_node_094311))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_094341 else g32p_supplierForest_node_094360) else (if i.val < 11 then g32p_supplierForest_node_094371 else g32p_supplierForest_node_094382)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_094402 else g32p_supplierForest_node_094404) else (if i.val < 15 then g32p_supplierForest_node_094405 else g32p_supplierForest_node_094421)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_094436 else g32p_supplierForest_node_094439) else (if i.val < 19 then g32p_supplierForest_node_094445 else g32p_supplierForest_node_094464)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_094483 else g32p_supplierForest_node_094510) else (if i.val < 23 then g32p_supplierForest_node_094521 else g32p_supplierForest_node_094523))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_094528 else g32p_supplierForest_node_094563) else (if i.val < 27 then g32p_supplierForest_node_094581 else g32p_supplierForest_node_094591)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_094593 else g32p_supplierForest_node_094617) else (if i.val < 31 then g32p_supplierForest_node_094662 else g32p_supplierForest_node_094673))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_094697 else g32p_supplierForest_node_094745) else (if i.val < 35 then g32p_supplierForest_node_094747 else g32p_supplierForest_node_094748)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_094809 else g32p_supplierForest_node_094842) else (if i.val < 39 then g32p_supplierForest_node_094850 else g32p_supplierForest_node_094863))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_094875 else g32p_supplierForest_node_094885) else (if i.val < 43 then g32p_supplierForest_node_094900 else g32p_supplierForest_node_094947)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_094948 else g32p_supplierForest_node_095016) else (if i.val < 47 then g32p_supplierForest_node_095018 else g32p_supplierForest_node_095102)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_095112 else g32p_supplierForest_node_095130) else (if i.val < 51 then g32p_supplierForest_node_095164 else g32p_supplierForest_node_095180)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_095226 else g32p_supplierForest_node_095228) else (if i.val < 55 then g32p_supplierForest_node_095229 else g32p_supplierForest_node_095232))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_095237 else g32p_supplierForest_node_095249) else (if i.val < 59 then g32p_supplierForest_node_095265 else g32p_supplierForest_node_095275)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_095279 else g32p_supplierForest_node_095303) else (if i.val < 63 then g32p_supplierForest_node_095316 else g32p_supplierForest_node_095350)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_095416 else g32p_supplierForest_node_095426) else (if i.val < 67 then g32p_supplierForest_node_095435 else g32p_supplierForest_node_095469)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_095515 else g32p_supplierForest_node_095517) else (if i.val < 71 then g32p_supplierForest_node_095529 else g32p_supplierForest_node_095616))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_095623 else g32p_supplierForest_node_095632) else (if i.val < 75 then g32p_supplierForest_node_095643 else g32p_supplierForest_node_095684)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_095709 else g32p_supplierForest_node_095734) else (if i.val < 79 then g32p_supplierForest_node_095748 else g32p_supplierForest_node_095756)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_095839 else g32p_supplierForest_node_095854) else (if i.val < 83 then g32p_supplierForest_node_095858 else g32p_supplierForest_node_095882)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_095897 else g32p_supplierForest_node_095924) else (if i.val < 87 then g32p_supplierForest_node_095955 else g32p_supplierForest_node_095961))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_095996 else g32p_supplierForest_node_096006) else (if i.val < 91 then g32p_supplierForest_node_096017 else g32p_supplierForest_node_096024)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_096029 else g32p_supplierForest_node_096045) else (if i.val < 95 then g32p_supplierForest_node_096083 else g32p_supplierForest_node_096093))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_096109 else g32p_supplierForest_node_096112) else (if i.val < 99 then g32p_supplierForest_node_096219 else g32p_supplierForest_node_096223)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_096255 else g32p_supplierForest_node_096258) else (if i.val < 103 then g32p_supplierForest_node_096266 else g32p_supplierForest_node_096273))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_096296 else g32p_supplierForest_node_096312) else (if i.val < 107 then g32p_supplierForest_node_096386 else g32p_supplierForest_node_096407)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_096421 else g32p_supplierForest_node_096438) else (if i.val < 111 then g32p_supplierForest_node_096439 else g32p_supplierForest_node_096454)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_096473 else g32p_supplierForest_node_096486) else (if i.val < 115 then g32p_supplierForest_node_096510 else g32p_supplierForest_node_096548)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_096555 else g32p_supplierForest_node_096563) else (if i.val < 119 then g32p_supplierForest_node_096596 else g32p_supplierForest_node_096606))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_096647 else g32p_supplierForest_node_096660) else (if i.val < 123 then g32p_supplierForest_node_096673 else g32p_supplierForest_node_096674)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_096679 else g32p_supplierForest_node_096691) else (if i.val < 127 then g32p_supplierForest_node_096712 else g32p_supplierForest_node_096725))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_096793 else g32p_supplierForest_node_096802) else (if i.val < 131 then g32p_supplierForest_node_096806 else g32p_supplierForest_node_096808)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_096814 else g32p_supplierForest_node_096816) else (if i.val < 135 then g32p_supplierForest_node_096859 else g32p_supplierForest_node_096869))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_096877 else g32p_supplierForest_node_096984) else (if i.val < 139 then g32p_supplierForest_node_097036 else g32p_supplierForest_node_097080)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_097090 else g32p_supplierForest_node_097103) else (if i.val < 143 then g32p_supplierForest_node_097112 else g32p_supplierForest_node_097136)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_097158 else g32p_supplierForest_node_097203) else (if i.val < 147 then g32p_supplierForest_node_097236 else g32p_supplierForest_node_097238)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_097252 else g32p_supplierForest_node_097264) else (if i.val < 151 then g32p_supplierForest_node_097279 else g32p_supplierForest_node_097280))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_097312 else g32p_supplierForest_node_097314) else (if i.val < 155 then g32p_supplierForest_node_097321 else g32p_supplierForest_node_097341)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_097346 else g32p_supplierForest_node_097369) else (if i.val < 159 then g32p_supplierForest_node_097370 else g32p_supplierForest_node_097428))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_097439 else g32p_supplierForest_node_097480) else (if i.val < 163 then g32p_supplierForest_node_097490 else g32p_supplierForest_node_097491)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_097504 else g32p_supplierForest_node_097520) else (if i.val < 167 then g32p_supplierForest_node_097522 else g32p_supplierForest_node_097576))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_097657 else g32p_supplierForest_node_097710) else (if i.val < 171 then g32p_supplierForest_node_097716 else g32p_supplierForest_node_097717)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_097728 else g32p_supplierForest_node_097755) else (if i.val < 175 then g32p_supplierForest_node_097766 else g32p_supplierForest_node_097769)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_097787 else g32p_supplierForest_node_097789) else (if i.val < 179 then g32p_supplierForest_node_097838 else g32p_supplierForest_node_097867)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_097885 else g32p_supplierForest_node_097888) else (if i.val < 183 then g32p_supplierForest_node_097908 else g32p_supplierForest_node_097920))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_097938 else g32p_supplierForest_node_097957) else (if i.val < 187 then g32p_supplierForest_node_097989 else g32p_supplierForest_node_098037)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_098076 else g32p_supplierForest_node_098112) else (if i.val < 191 then g32p_supplierForest_node_098130 else g32p_supplierForest_node_098157)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_098191 else g32p_supplierForest_node_098195) else (if i.val < 195 then g32p_supplierForest_node_098205 else g32p_supplierForest_node_098226)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_098292 else g32p_supplierForest_node_098304) else (if i.val < 199 then g32p_supplierForest_node_098305 else g32p_supplierForest_node_098348))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_098391 else g32p_supplierForest_node_098415) else (if i.val < 203 then g32p_supplierForest_node_098447 else g32p_supplierForest_node_098489)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_098514 else g32p_supplierForest_node_098525) else (if i.val < 207 then g32p_supplierForest_node_098555 else g32p_supplierForest_node_098566)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_098586 else g32p_supplierForest_node_098602) else (if i.val < 211 then g32p_supplierForest_node_098613 else g32p_supplierForest_node_098616)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_098645 else g32p_supplierForest_node_098658) else (if i.val < 215 then g32p_supplierForest_node_098678 else g32p_supplierForest_node_098705))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_098715 else g32p_supplierForest_node_098738) else (if i.val < 219 then g32p_supplierForest_node_098783 else g32p_supplierForest_node_098786)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_098798 else g32p_supplierForest_node_098811) else (if i.val < 223 then g32p_supplierForest_node_098813 else g32p_supplierForest_node_098841))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_098853 else g32p_supplierForest_node_098875) else (if i.val < 227 then g32p_supplierForest_node_098893 else g32p_supplierForest_node_098914)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_098931 else g32p_supplierForest_node_098969) else (if i.val < 231 then g32p_supplierForest_node_098987 else g32p_supplierForest_node_099002))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_099006 else g32p_supplierForest_node_099061) else (if i.val < 235 then g32p_supplierForest_node_099086 else g32p_supplierForest_node_099124)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_099151 else g32p_supplierForest_node_099205) else (if i.val < 239 then g32p_supplierForest_node_099220 else g32p_supplierForest_node_099223)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_099231 else g32p_supplierForest_node_099254) else (if i.val < 243 then g32p_supplierForest_node_099258 else g32p_supplierForest_node_099280)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_099287 else g32p_supplierForest_node_099321) else (if i.val < 247 then g32p_supplierForest_node_099331 else g32p_supplierForest_node_099350))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_099368 else g32p_supplierForest_node_099383) else (if i.val < 251 then g32p_supplierForest_node_099396 else g32p_supplierForest_node_099405)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_099413 else g32p_supplierForest_node_099417) else (if i.val < 255 then g32p_supplierForest_node_099419 else g32p_supplierForest_node_099452))))))))

def g32p_supplierForest_classes_101 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 26 else 46) else (if i.val < 3 then 49 else 47)) else (if i.val < 6 then (if i.val < 5 then 49 else 81) else (if i.val < 7 then 11 else 85))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 13 else 49) else (if i.val < 11 then 49 else 46)) else (if i.val < 14 then (if i.val < 13 then 47 else 47) else (if i.val < 15 then 46 else 46)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 45 else 46) else (if i.val < 19 then 46 else 46)) else (if i.val < 22 then (if i.val < 21 then 45 else 46) else (if i.val < 23 then 46 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 46 else 50) else (if i.val < 27 then 46 else 84)) else (if i.val < 30 then (if i.val < 29 then 49 else 47) else (if i.val < 31 then 49 else 49))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 47 else 49) else (if i.val < 35 then 46 else 13)) else (if i.val < 38 then (if i.val < 37 then 49 else 47) else (if i.val < 39 then 55 else 53))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 47 else 26) else (if i.val < 43 then 47 else 25)) else (if i.val < 46 then (if i.val < 45 then 49 else 25) else (if i.val < 47 then 49 else 46)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 9) else (if i.val < 51 then 47 else 50)) else (if i.val < 54 then (if i.val < 53 then 56 else 49) else (if i.val < 55 then 86 else 46))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 46 else 25) else (if i.val < 59 then 46 else 25)) else (if i.val < 62 then (if i.val < 61 then 25 else 49) else (if i.val < 63 then 81 else 49)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 46 else 46) else (if i.val < 67 then 46 else 55)) else (if i.val < 70 then (if i.val < 69 then 26 else 49) else (if i.val < 71 then 47 else 46))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 80 else 47) else (if i.val < 75 then 46 else 49)) else (if i.val < 78 then (if i.val < 77 then 25 else 49) else (if i.val < 79 then 47 else 52)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 26 else 49) else (if i.val < 83 then 49 else 49)) else (if i.val < 86 then (if i.val < 85 then 26 else 45) else (if i.val < 87 then 46 else 49))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 50 else 46) else (if i.val < 91 then 25 else 45)) else (if i.val < 94 then (if i.val < 93 then 50 else 53) else (if i.val < 95 then 49 else 46))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 49 else 80) else (if i.val < 99 then 86 else 53)) else (if i.val < 102 then (if i.val < 101 then 55 else 54) else (if i.val < 103 then 84 else 46))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 49 else 48) else (if i.val < 107 then 46 else 47)) else (if i.val < 110 then (if i.val < 109 then 49 else 55) else (if i.val < 111 then 56 else 49)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 49 else 49) else (if i.val < 115 then 46 else 54)) else (if i.val < 118 then (if i.val < 117 then 46 else 49) else (if i.val < 119 then 26 else 84))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 25 else 26) else (if i.val < 123 then 53 else 49)) else (if i.val < 126 then (if i.val < 125 then 83 else 9) else (if i.val < 127 then 27 else 25))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 49 else 54) else (if i.val < 131 then 49 else 25)) else (if i.val < 134 then (if i.val < 133 then 53 else 49) else (if i.val < 135 then 50 else 49))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 49 else 46) else (if i.val < 139 then 49 else 45)) else (if i.val < 142 then (if i.val < 141 then 84 else 25) else (if i.val < 143 then 47 else 50)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 55 else 25) else (if i.val < 147 then 46 else 26)) else (if i.val < 150 then (if i.val < 149 then 54 else 55) else (if i.val < 151 then 26 else 46))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 49 else 47) else (if i.val < 155 then 46 else 47)) else (if i.val < 158 then (if i.val < 157 then 26 else 81) else (if i.val < 159 then 27 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 45 else 46) else (if i.val < 163 then 80 else 49)) else (if i.val < 166 then (if i.val < 165 then 25 else 46) else (if i.val < 167 then 46 else 49))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 53) else (if i.val < 171 then 54 else 49)) else (if i.val < 174 then (if i.val < 173 then 25 else 53) else (if i.val < 175 then 46 else 84)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 84 else 83) else (if i.val < 179 then 55 else 13)) else (if i.val < 182 then (if i.val < 181 then 49 else 49) else (if i.val < 183 then 46 else 80))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 82 else 49) else (if i.val < 187 then 80 else 49)) else (if i.val < 190 then (if i.val < 189 then 46 else 49) else (if i.val < 191 then 12 else 26)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 47 else 46) else (if i.val < 195 then 46 else 46)) else (if i.val < 198 then (if i.val < 197 then 47 else 49) else (if i.val < 199 then 49 else 50))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 56 else 80) else (if i.val < 203 then 49 else 26)) else (if i.val < 206 then (if i.val < 205 then 49 else 25) else (if i.val < 207 then 83 else 26)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 53 else 46) else (if i.val < 211 then 12 else 54)) else (if i.val < 214 then (if i.val < 213 then 46 else 26) else (if i.val < 215 then 46 else 46))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 55 else 84) else (if i.val < 219 then 27 else 26)) else (if i.val < 222 then (if i.val < 221 then 49 else 13) else (if i.val < 223 then 50 else 46))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 50 else 50) else (if i.val < 227 then 80 else 49)) else (if i.val < 230 then (if i.val < 229 then 49 else 55) else (if i.val < 231 then 25 else 45))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 46 else 9) else (if i.val < 235 then 49 else 54)) else (if i.val < 238 then (if i.val < 237 then 49 else 26) else (if i.val < 239 then 26 else 85)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 45 else 49) else (if i.val < 243 then 54 else 25)) else (if i.val < 246 then (if i.val < 245 then 49 else 50) else (if i.val < 247 then 26 else 46))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 55 else 26) else (if i.val < 251 then 49 else 52)) else (if i.val < 254 then (if i.val < 253 then 54 else 46) else (if i.val < 255 then 45 else 47))))))))

theorem g32p_supplierForest_actual_101 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_101 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_101 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_094191
  · exact g32p_supplierForest_actual_094204
  · exact g32p_supplierForest_actual_094232
  · exact g32p_supplierForest_actual_094243
  · exact g32p_supplierForest_actual_094287
  · exact g32p_supplierForest_actual_094295
  · exact g32p_supplierForest_actual_094302
  · exact g32p_supplierForest_actual_094311
  · exact g32p_supplierForest_actual_094341
  · exact g32p_supplierForest_actual_094360
  · exact g32p_supplierForest_actual_094371
  · exact g32p_supplierForest_actual_094382
  · exact g32p_supplierForest_actual_094402
  · exact g32p_supplierForest_actual_094404
  · exact g32p_supplierForest_actual_094405
  · exact g32p_supplierForest_actual_094421
  · exact g32p_supplierForest_actual_094436
  · exact g32p_supplierForest_actual_094439
  · exact g32p_supplierForest_actual_094445
  · exact g32p_supplierForest_actual_094464
  · exact g32p_supplierForest_actual_094483
  · exact g32p_supplierForest_actual_094510
  · exact g32p_supplierForest_actual_094521
  · exact g32p_supplierForest_actual_094523
  · exact g32p_supplierForest_actual_094528
  · exact g32p_supplierForest_actual_094563
  · exact g32p_supplierForest_actual_094581
  · exact g32p_supplierForest_actual_094591
  · exact g32p_supplierForest_actual_094593
  · exact g32p_supplierForest_actual_094617
  · exact g32p_supplierForest_actual_094662
  · exact g32p_supplierForest_actual_094673
  · exact g32p_supplierForest_actual_094697
  · exact g32p_supplierForest_actual_094745
  · exact g32p_supplierForest_actual_094747
  · exact g32p_supplierForest_actual_094748
  · exact g32p_supplierForest_actual_094809
  · exact g32p_supplierForest_actual_094842
  · exact g32p_supplierForest_actual_094850
  · exact g32p_supplierForest_actual_094863
  · exact g32p_supplierForest_actual_094875
  · exact g32p_supplierForest_actual_094885
  · exact g32p_supplierForest_actual_094900
  · exact g32p_supplierForest_actual_094947
  · exact g32p_supplierForest_actual_094948
  · exact g32p_supplierForest_actual_095016
  · exact g32p_supplierForest_actual_095018
  · exact g32p_supplierForest_actual_095102
  · exact g32p_supplierForest_actual_095112
  · exact g32p_supplierForest_actual_095130
  · exact g32p_supplierForest_actual_095164
  · exact g32p_supplierForest_actual_095180
  · exact g32p_supplierForest_actual_095226
  · exact g32p_supplierForest_actual_095228
  · exact g32p_supplierForest_actual_095229
  · exact g32p_supplierForest_actual_095232
  · exact g32p_supplierForest_actual_095237
  · exact g32p_supplierForest_actual_095249
  · exact g32p_supplierForest_actual_095265
  · exact g32p_supplierForest_actual_095275
  · exact g32p_supplierForest_actual_095279
  · exact g32p_supplierForest_actual_095303
  · exact g32p_supplierForest_actual_095316
  · exact g32p_supplierForest_actual_095350
  · exact g32p_supplierForest_actual_095416
  · exact g32p_supplierForest_actual_095426
  · exact g32p_supplierForest_actual_095435
  · exact g32p_supplierForest_actual_095469
  · exact g32p_supplierForest_actual_095515
  · exact g32p_supplierForest_actual_095517
  · exact g32p_supplierForest_actual_095529
  · exact g32p_supplierForest_actual_095616
  · exact g32p_supplierForest_actual_095623
  · exact g32p_supplierForest_actual_095632
  · exact g32p_supplierForest_actual_095643
  · exact g32p_supplierForest_actual_095684
  · exact g32p_supplierForest_actual_095709
  · exact g32p_supplierForest_actual_095734
  · exact g32p_supplierForest_actual_095748
  · exact g32p_supplierForest_actual_095756
  · exact g32p_supplierForest_actual_095839
  · exact g32p_supplierForest_actual_095854
  · exact g32p_supplierForest_actual_095858
  · exact g32p_supplierForest_actual_095882
  · exact g32p_supplierForest_actual_095897
  · exact g32p_supplierForest_actual_095924
  · exact g32p_supplierForest_actual_095955
  · exact g32p_supplierForest_actual_095961
  · exact g32p_supplierForest_actual_095996
  · exact g32p_supplierForest_actual_096006
  · exact g32p_supplierForest_actual_096017
  · exact g32p_supplierForest_actual_096024
  · exact g32p_supplierForest_actual_096029
  · exact g32p_supplierForest_actual_096045
  · exact g32p_supplierForest_actual_096083
  · exact g32p_supplierForest_actual_096093
  · exact g32p_supplierForest_actual_096109
  · exact g32p_supplierForest_actual_096112
  · exact g32p_supplierForest_actual_096219
  · exact g32p_supplierForest_actual_096223
  · exact g32p_supplierForest_actual_096255
  · exact g32p_supplierForest_actual_096258
  · exact g32p_supplierForest_actual_096266
  · exact g32p_supplierForest_actual_096273
  · exact g32p_supplierForest_actual_096296
  · exact g32p_supplierForest_actual_096312
  · exact g32p_supplierForest_actual_096386
  · exact g32p_supplierForest_actual_096407
  · exact g32p_supplierForest_actual_096421
  · exact g32p_supplierForest_actual_096438
  · exact g32p_supplierForest_actual_096439
  · exact g32p_supplierForest_actual_096454
  · exact g32p_supplierForest_actual_096473
  · exact g32p_supplierForest_actual_096486
  · exact g32p_supplierForest_actual_096510
  · exact g32p_supplierForest_actual_096548
  · exact g32p_supplierForest_actual_096555
  · exact g32p_supplierForest_actual_096563
  · exact g32p_supplierForest_actual_096596
  · exact g32p_supplierForest_actual_096606
  · exact g32p_supplierForest_actual_096647
  · exact g32p_supplierForest_actual_096660
  · exact g32p_supplierForest_actual_096673
  · exact g32p_supplierForest_actual_096674
  · exact g32p_supplierForest_actual_096679
  · exact g32p_supplierForest_actual_096691
  · exact g32p_supplierForest_actual_096712
  · exact g32p_supplierForest_actual_096725
  · exact g32p_supplierForest_actual_096793
  · exact g32p_supplierForest_actual_096802
  · exact g32p_supplierForest_actual_096806
  · exact g32p_supplierForest_actual_096808
  · exact g32p_supplierForest_actual_096814
  · exact g32p_supplierForest_actual_096816
  · exact g32p_supplierForest_actual_096859
  · exact g32p_supplierForest_actual_096869
  · exact g32p_supplierForest_actual_096877
  · exact g32p_supplierForest_actual_096984
  · exact g32p_supplierForest_actual_097036
  · exact g32p_supplierForest_actual_097080
  · exact g32p_supplierForest_actual_097090
  · exact g32p_supplierForest_actual_097103
  · exact g32p_supplierForest_actual_097112
  · exact g32p_supplierForest_actual_097136
  · exact g32p_supplierForest_actual_097158
  · exact g32p_supplierForest_actual_097203
  · exact g32p_supplierForest_actual_097236
  · exact g32p_supplierForest_actual_097238
  · exact g32p_supplierForest_actual_097252
  · exact g32p_supplierForest_actual_097264
  · exact g32p_supplierForest_actual_097279
  · exact g32p_supplierForest_actual_097280
  · exact g32p_supplierForest_actual_097312
  · exact g32p_supplierForest_actual_097314
  · exact g32p_supplierForest_actual_097321
  · exact g32p_supplierForest_actual_097341
  · exact g32p_supplierForest_actual_097346
  · exact g32p_supplierForest_actual_097369
  · exact g32p_supplierForest_actual_097370
  · exact g32p_supplierForest_actual_097428
  · exact g32p_supplierForest_actual_097439
  · exact g32p_supplierForest_actual_097480
  · exact g32p_supplierForest_actual_097490
  · exact g32p_supplierForest_actual_097491
  · exact g32p_supplierForest_actual_097504
  · exact g32p_supplierForest_actual_097520
  · exact g32p_supplierForest_actual_097522
  · exact g32p_supplierForest_actual_097576
  · exact g32p_supplierForest_actual_097657
  · exact g32p_supplierForest_actual_097710
  · exact g32p_supplierForest_actual_097716
  · exact g32p_supplierForest_actual_097717
  · exact g32p_supplierForest_actual_097728
  · exact g32p_supplierForest_actual_097755
  · exact g32p_supplierForest_actual_097766
  · exact g32p_supplierForest_actual_097769
  · exact g32p_supplierForest_actual_097787
  · exact g32p_supplierForest_actual_097789
  · exact g32p_supplierForest_actual_097838
  · exact g32p_supplierForest_actual_097867
  · exact g32p_supplierForest_actual_097885
  · exact g32p_supplierForest_actual_097888
  · exact g32p_supplierForest_actual_097908
  · exact g32p_supplierForest_actual_097920
  · exact g32p_supplierForest_actual_097938
  · exact g32p_supplierForest_actual_097957
  · exact g32p_supplierForest_actual_097989
  · exact g32p_supplierForest_actual_098037
  · exact g32p_supplierForest_actual_098076
  · exact g32p_supplierForest_actual_098112
  · exact g32p_supplierForest_actual_098130
  · exact g32p_supplierForest_actual_098157
  · exact g32p_supplierForest_actual_098191
  · exact g32p_supplierForest_actual_098195
  · exact g32p_supplierForest_actual_098205
  · exact g32p_supplierForest_actual_098226
  · exact g32p_supplierForest_actual_098292
  · exact g32p_supplierForest_actual_098304
  · exact g32p_supplierForest_actual_098305
  · exact g32p_supplierForest_actual_098348
  · exact g32p_supplierForest_actual_098391
  · exact g32p_supplierForest_actual_098415
  · exact g32p_supplierForest_actual_098447
  · exact g32p_supplierForest_actual_098489
  · exact g32p_supplierForest_actual_098514
  · exact g32p_supplierForest_actual_098525
  · exact g32p_supplierForest_actual_098555
  · exact g32p_supplierForest_actual_098566
  · exact g32p_supplierForest_actual_098586
  · exact g32p_supplierForest_actual_098602
  · exact g32p_supplierForest_actual_098613
  · exact g32p_supplierForest_actual_098616
  · exact g32p_supplierForest_actual_098645
  · exact g32p_supplierForest_actual_098658
  · exact g32p_supplierForest_actual_098678
  · exact g32p_supplierForest_actual_098705
  · exact g32p_supplierForest_actual_098715
  · exact g32p_supplierForest_actual_098738
  · exact g32p_supplierForest_actual_098783
  · exact g32p_supplierForest_actual_098786
  · exact g32p_supplierForest_actual_098798
  · exact g32p_supplierForest_actual_098811
  · exact g32p_supplierForest_actual_098813
  · exact g32p_supplierForest_actual_098841
  · exact g32p_supplierForest_actual_098853
  · exact g32p_supplierForest_actual_098875
  · exact g32p_supplierForest_actual_098893
  · exact g32p_supplierForest_actual_098914
  · exact g32p_supplierForest_actual_098931
  · exact g32p_supplierForest_actual_098969
  · exact g32p_supplierForest_actual_098987
  · exact g32p_supplierForest_actual_099002
  · exact g32p_supplierForest_actual_099006
  · exact g32p_supplierForest_actual_099061
  · exact g32p_supplierForest_actual_099086
  · exact g32p_supplierForest_actual_099124
  · exact g32p_supplierForest_actual_099151
  · exact g32p_supplierForest_actual_099205
  · exact g32p_supplierForest_actual_099220
  · exact g32p_supplierForest_actual_099223
  · exact g32p_supplierForest_actual_099231
  · exact g32p_supplierForest_actual_099254
  · exact g32p_supplierForest_actual_099258
  · exact g32p_supplierForest_actual_099280
  · exact g32p_supplierForest_actual_099287
  · exact g32p_supplierForest_actual_099321
  · exact g32p_supplierForest_actual_099331
  · exact g32p_supplierForest_actual_099350
  · exact g32p_supplierForest_actual_099368
  · exact g32p_supplierForest_actual_099383
  · exact g32p_supplierForest_actual_099396
  · exact g32p_supplierForest_actual_099405
  · exact g32p_supplierForest_actual_099413
  · exact g32p_supplierForest_actual_099417
  · exact g32p_supplierForest_actual_099419
  · exact g32p_supplierForest_actual_099452

def g32p_supplierForest_nodes_102 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_099494 else g32p_supplierForest_node_099532) else (if i.val < 3 then g32p_supplierForest_node_099545 else g32p_supplierForest_node_099546)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_099562 else g32p_supplierForest_node_099566) else (if i.val < 7 then g32p_supplierForest_node_099574 else g32p_supplierForest_node_099601))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_099623 else g32p_supplierForest_node_099675) else (if i.val < 11 then g32p_supplierForest_node_099678 else g32p_supplierForest_node_099703)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_099745 else g32p_supplierForest_node_099759) else (if i.val < 15 then g32p_supplierForest_node_099834 else g32p_supplierForest_node_099846)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_099859 else g32p_supplierForest_node_099861) else (if i.val < 19 then g32p_supplierForest_node_099896 else g32p_supplierForest_node_099910)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_100018 else g32p_supplierForest_node_100093) else (if i.val < 23 then g32p_supplierForest_node_100121 else g32p_supplierForest_node_100144))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_100157 else g32p_supplierForest_node_100170) else (if i.val < 27 then g32p_supplierForest_node_100192 else g32p_supplierForest_node_100199)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_100224 else g32p_supplierForest_node_100236) else (if i.val < 31 then g32p_supplierForest_node_100248 else g32p_supplierForest_node_100256))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_100263 else g32p_supplierForest_node_100277) else (if i.val < 35 then g32p_supplierForest_node_100278 else g32p_supplierForest_node_100299)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_100329 else g32p_supplierForest_node_100339) else (if i.val < 39 then g32p_supplierForest_node_100383 else g32p_supplierForest_node_100386))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_100459 else g32p_supplierForest_node_100474) else (if i.val < 43 then g32p_supplierForest_node_100490 else g32p_supplierForest_node_100507)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_100530 else g32p_supplierForest_node_100553) else (if i.val < 47 then g32p_supplierForest_node_100564 else g32p_supplierForest_node_100566)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_100574 else g32p_supplierForest_node_100600) else (if i.val < 51 then g32p_supplierForest_node_100665 else g32p_supplierForest_node_100690)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_100694 else g32p_supplierForest_node_100719) else (if i.val < 55 then g32p_supplierForest_node_100812 else g32p_supplierForest_node_100824))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_100849 else g32p_supplierForest_node_100855) else (if i.val < 59 then g32p_supplierForest_node_100895 else g32p_supplierForest_node_100901)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_100932 else g32p_supplierForest_node_100944) else (if i.val < 63 then g32p_supplierForest_node_100950 else g32p_supplierForest_node_100978)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_101009 else g32p_supplierForest_node_101016) else (if i.val < 67 then g32p_supplierForest_node_101024 else g32p_supplierForest_node_101027)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_101060 else g32p_supplierForest_node_101076) else (if i.val < 71 then g32p_supplierForest_node_101095 else g32p_supplierForest_node_101133))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_101145 else g32p_supplierForest_node_101159) else (if i.val < 75 then g32p_supplierForest_node_101160 else g32p_supplierForest_node_101185)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_101196 else g32p_supplierForest_node_101208) else (if i.val < 79 then g32p_supplierForest_node_101214 else g32p_supplierForest_node_101225)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_101245 else g32p_supplierForest_node_101250) else (if i.val < 83 then g32p_supplierForest_node_101264 else g32p_supplierForest_node_101275)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_101283 else g32p_supplierForest_node_101316) else (if i.val < 87 then g32p_supplierForest_node_101342 else g32p_supplierForest_node_101344))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_101360 else g32p_supplierForest_node_101371) else (if i.val < 91 then g32p_supplierForest_node_101386 else g32p_supplierForest_node_101396)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_101397 else g32p_supplierForest_node_101427) else (if i.val < 95 then g32p_supplierForest_node_101429 else g32p_supplierForest_node_101442))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_101451 else g32p_supplierForest_node_101469) else (if i.val < 99 then g32p_supplierForest_node_101471 else g32p_supplierForest_node_101499)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_101523 else g32p_supplierForest_node_101572) else (if i.val < 103 then g32p_supplierForest_node_101582 else g32p_supplierForest_node_101589))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_101604 else g32p_supplierForest_node_101611) else (if i.val < 107 then g32p_supplierForest_node_101655 else g32p_supplierForest_node_101672)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_101677 else g32p_supplierForest_node_101698) else (if i.val < 111 then g32p_supplierForest_node_101703 else g32p_supplierForest_node_101716)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_101717 else g32p_supplierForest_node_101726) else (if i.val < 115 then g32p_supplierForest_node_101729 else g32p_supplierForest_node_101747)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_101777 else g32p_supplierForest_node_101805) else (if i.val < 119 then g32p_supplierForest_node_101835 else g32p_supplierForest_node_101841))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_101863 else g32p_supplierForest_node_101874) else (if i.val < 123 then g32p_supplierForest_node_101878 else g32p_supplierForest_node_101895)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_101900 else g32p_supplierForest_node_101933) else (if i.val < 127 then g32p_supplierForest_node_101950 else g32p_supplierForest_node_101951))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_101993 else g32p_supplierForest_node_102023) else (if i.val < 131 then g32p_supplierForest_node_102030 else g32p_supplierForest_node_102042)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_102053 else g32p_supplierForest_node_102065) else (if i.val < 135 then g32p_supplierForest_node_102115 else g32p_supplierForest_node_102127))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_102135 else g32p_supplierForest_node_102148) else (if i.val < 139 then g32p_supplierForest_node_102154 else g32p_supplierForest_node_102161)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_102194 else g32p_supplierForest_node_102205) else (if i.val < 143 then g32p_supplierForest_node_102224 else g32p_supplierForest_node_102241)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_102244 else g32p_supplierForest_node_102250) else (if i.val < 147 then g32p_supplierForest_node_102282 else g32p_supplierForest_node_102284)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_102310 else g32p_supplierForest_node_102317) else (if i.val < 151 then g32p_supplierForest_node_102386 else g32p_supplierForest_node_102411))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_102412 else g32p_supplierForest_node_102416) else (if i.val < 155 then g32p_supplierForest_node_102498 else g32p_supplierForest_node_102503)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_102504 else g32p_supplierForest_node_102521) else (if i.val < 159 then g32p_supplierForest_node_102537 else g32p_supplierForest_node_102551))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_102552 else g32p_supplierForest_node_102597) else (if i.val < 163 then g32p_supplierForest_node_102614 else g32p_supplierForest_node_102619)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_102629 else g32p_supplierForest_node_102640) else (if i.val < 167 then g32p_supplierForest_node_102656 else g32p_supplierForest_node_102682))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_102687 else g32p_supplierForest_node_102697) else (if i.val < 171 then g32p_supplierForest_node_102707 else g32p_supplierForest_node_102718)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_102741 else g32p_supplierForest_node_102764) else (if i.val < 175 then g32p_supplierForest_node_102786 else g32p_supplierForest_node_102842)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_102843 else g32p_supplierForest_node_102858) else (if i.val < 179 then g32p_supplierForest_node_102861 else g32p_supplierForest_node_102873)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_102893 else g32p_supplierForest_node_102927) else (if i.val < 183 then g32p_supplierForest_node_102943 else g32p_supplierForest_node_102985))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_103013 else g32p_supplierForest_node_103014) else (if i.val < 187 then g32p_supplierForest_node_103020 else g32p_supplierForest_node_103034)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_103043 else g32p_supplierForest_node_103087) else (if i.val < 191 then g32p_supplierForest_node_103105 else g32p_supplierForest_node_103121)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_103170 else g32p_supplierForest_node_103203) else (if i.val < 195 then g32p_supplierForest_node_103227 else g32p_supplierForest_node_103239)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_103244 else g32p_supplierForest_node_103257) else (if i.val < 199 then g32p_supplierForest_node_103260 else g32p_supplierForest_node_103306))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_103340 else g32p_supplierForest_node_103365) else (if i.val < 203 then g32p_supplierForest_node_103385 else g32p_supplierForest_node_103400)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_103422 else g32p_supplierForest_node_103435) else (if i.val < 207 then g32p_supplierForest_node_103438 else g32p_supplierForest_node_103439)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_103452 else g32p_supplierForest_node_103532) else (if i.val < 211 then g32p_supplierForest_node_103545 else g32p_supplierForest_node_103560)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_103612 else g32p_supplierForest_node_103644) else (if i.val < 215 then g32p_supplierForest_node_103647 else g32p_supplierForest_node_103655))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_103667 else g32p_supplierForest_node_103678) else (if i.val < 219 then g32p_supplierForest_node_103685 else g32p_supplierForest_node_103703)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_103723 else g32p_supplierForest_node_103805) else (if i.val < 223 then g32p_supplierForest_node_103836 else g32p_supplierForest_node_103861))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_103868 else g32p_supplierForest_node_103878) else (if i.val < 227 then g32p_supplierForest_node_103882 else g32p_supplierForest_node_103891)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_103901 else g32p_supplierForest_node_103964) else (if i.val < 231 then g32p_supplierForest_node_103979 else g32p_supplierForest_node_104038))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_104054 else g32p_supplierForest_node_104069) else (if i.val < 235 then g32p_supplierForest_node_104100 else g32p_supplierForest_node_104156)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_104160 else g32p_supplierForest_node_104194) else (if i.val < 239 then g32p_supplierForest_node_104198 else g32p_supplierForest_node_104221)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_104236 else g32p_supplierForest_node_104243) else (if i.val < 243 then g32p_supplierForest_node_104245 else g32p_supplierForest_node_104247)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_104261 else g32p_supplierForest_node_104268) else (if i.val < 247 then g32p_supplierForest_node_104269 else g32p_supplierForest_node_104308))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_104329 else g32p_supplierForest_node_104343) else (if i.val < 251 then g32p_supplierForest_node_104344 else g32p_supplierForest_node_104364)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_104365 else g32p_supplierForest_node_104407) else (if i.val < 255 then g32p_supplierForest_node_104434 else g32p_supplierForest_node_104438))))))))

def g32p_supplierForest_classes_102 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 49 else 13) else (if i.val < 3 then 49 else 49)) else (if i.val < 6 then (if i.val < 5 then 49 else 80) else (if i.val < 7 then 55 else 55))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 86 else 26) else (if i.val < 11 then 52 else 47)) else (if i.val < 14 then (if i.val < 13 then 55 else 47) else (if i.val < 15 then 49 else 25)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 49 else 80) else (if i.val < 19 then 46 else 25)) else (if i.val < 22 then (if i.val < 21 then 80 else 26) else (if i.val < 23 then 49 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 25 else 49) else (if i.val < 27 then 53 else 49)) else (if i.val < 30 then (if i.val < 29 then 49 else 55) else (if i.val < 31 then 46 else 49))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 50 else 49) else (if i.val < 35 then 49 else 84)) else (if i.val < 38 then (if i.val < 37 then 49 else 46) else (if i.val < 39 then 13 else 50))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 49 else 80) else (if i.val < 43 then 54 else 53)) else (if i.val < 46 then (if i.val < 45 then 52 else 80) else (if i.val < 47 then 46 else 80)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 45 else 26) else (if i.val < 51 then 55 else 49)) else (if i.val < 54 then (if i.val < 53 then 80 else 26) else (if i.val < 55 then 25 else 25))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 50 else 46) else (if i.val < 59 then 86 else 46)) else (if i.val < 62 then (if i.val < 61 then 46 else 55) else (if i.val < 63 then 55 else 54)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 55 else 25) else (if i.val < 67 then 13 else 46)) else (if i.val < 70 then (if i.val < 69 then 49 else 25) else (if i.val < 71 then 25 else 25))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 54 else 26) else (if i.val < 75 then 26 else 47)) else (if i.val < 78 then (if i.val < 77 then 45 else 86) else (if i.val < 79 then 46 else 80)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 49 else 47) else (if i.val < 83 then 86 else 13)) else (if i.val < 86 then (if i.val < 85 then 13 else 49) else (if i.val < 87 then 26 else 25))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 54 else 49) else (if i.val < 91 then 11 else 49)) else (if i.val < 94 then (if i.val < 93 then 49 else 47) else (if i.val < 95 then 52 else 53))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 26 else 13) else (if i.val < 99 then 46 else 25)) else (if i.val < 102 then (if i.val < 101 then 46 else 55) else (if i.val < 103 then 80 else 13))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 46 else 50) else (if i.val < 107 then 53 else 25)) else (if i.val < 110 then (if i.val < 109 then 55 else 13) else (if i.val < 111 then 46 else 46)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 46 else 25) else (if i.val < 115 then 25 else 54)) else (if i.val < 118 then (if i.val < 117 then 47 else 56) else (if i.val < 119 then 25 else 86))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 49 else 80) else (if i.val < 123 then 86 else 66)) else (if i.val < 126 then (if i.val < 125 then 57 else 57) else (if i.val < 127 then 59 else 57))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 59 else 29) else (if i.val < 131 then 29 else 16)) else (if i.val < 134 then (if i.val < 133 then 59 else 36) else (if i.val < 135 then 30 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 57 else 59) else (if i.val < 139 then 59 else 57)) else (if i.val < 142 then (if i.val < 141 then 61 else 15) else (if i.val < 143 then 58 else 59)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 57 else 62) else (if i.val < 147 then 57 else 57)) else (if i.val < 150 then (if i.val < 149 then 64 else 57) else (if i.val < 151 then 36 else 30))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 57) else (if i.val < 155 then 30 else 59)) else (if i.val < 158 then (if i.val < 157 then 59 else 17) else (if i.val < 159 then 15 else 30))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 30 else 57) else (if i.val < 163 then 36 else 57)) else (if i.val < 166 then (if i.val < 165 then 30 else 57) else (if i.val < 167 then 57 else 59))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 57 else 16) else (if i.val < 171 then 30 else 58)) else (if i.val < 174 then (if i.val < 173 then 58 else 57) else (if i.val < 175 then 59 else 33)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 36 else 59) else (if i.val < 179 then 29 else 30)) else (if i.val < 182 then (if i.val < 181 then 66 else 36) else (if i.val < 183 then 59 else 57))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 59 else 57) else (if i.val < 187 then 57 else 66)) else (if i.val < 190 then (if i.val < 189 then 57 else 16) else (if i.val < 191 then 16 else 16)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 30) else (if i.val < 195 then 16 else 57)) else (if i.val < 198 then (if i.val < 197 then 57 else 57) else (if i.val < 199 then 14 else 62))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 63 else 58) else (if i.val < 203 then 62 else 57)) else (if i.val < 206 then (if i.val < 205 then 63 else 16) else (if i.val < 207 then 57 else 16)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 57 else 57) else (if i.val < 211 then 66 else 30)) else (if i.val < 214 then (if i.val < 213 then 29 else 57) else (if i.val < 215 then 57 else 58))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 66 else 29) else (if i.val < 219 then 62 else 14)) else (if i.val < 222 then (if i.val < 221 then 57 else 62) else (if i.val < 223 then 66 else 29))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 4 else 57) else (if i.val < 227 then 57 else 57)) else (if i.val < 230 then (if i.val < 229 then 33 else 59) else (if i.val < 231 then 57 else 60))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 16 else 58) else (if i.val < 235 then 60 else 15)) else (if i.val < 238 then (if i.val < 237 then 29 else 34) else (if i.val < 239 then 30 else 29)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 62 else 34) else (if i.val < 243 then 60 else 29)) else (if i.val < 246 then (if i.val < 245 then 61 else 60) else (if i.val < 247 then 59 else 30))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 30 else 16) else (if i.val < 251 then 57 else 57)) else (if i.val < 254 then (if i.val < 253 then 30 else 29) else (if i.val < 255 then 57 else 58))))))))

theorem g32p_supplierForest_actual_102 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_102 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_102 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_099494
  · exact g32p_supplierForest_actual_099532
  · exact g32p_supplierForest_actual_099545
  · exact g32p_supplierForest_actual_099546
  · exact g32p_supplierForest_actual_099562
  · exact g32p_supplierForest_actual_099566
  · exact g32p_supplierForest_actual_099574
  · exact g32p_supplierForest_actual_099601
  · exact g32p_supplierForest_actual_099623
  · exact g32p_supplierForest_actual_099675
  · exact g32p_supplierForest_actual_099678
  · exact g32p_supplierForest_actual_099703
  · exact g32p_supplierForest_actual_099745
  · exact g32p_supplierForest_actual_099759
  · exact g32p_supplierForest_actual_099834
  · exact g32p_supplierForest_actual_099846
  · exact g32p_supplierForest_actual_099859
  · exact g32p_supplierForest_actual_099861
  · exact g32p_supplierForest_actual_099896
  · exact g32p_supplierForest_actual_099910
  · exact g32p_supplierForest_actual_100018
  · exact g32p_supplierForest_actual_100093
  · exact g32p_supplierForest_actual_100121
  · exact g32p_supplierForest_actual_100144
  · exact g32p_supplierForest_actual_100157
  · exact g32p_supplierForest_actual_100170
  · exact g32p_supplierForest_actual_100192
  · exact g32p_supplierForest_actual_100199
  · exact g32p_supplierForest_actual_100224
  · exact g32p_supplierForest_actual_100236
  · exact g32p_supplierForest_actual_100248
  · exact g32p_supplierForest_actual_100256
  · exact g32p_supplierForest_actual_100263
  · exact g32p_supplierForest_actual_100277
  · exact g32p_supplierForest_actual_100278
  · exact g32p_supplierForest_actual_100299
  · exact g32p_supplierForest_actual_100329
  · exact g32p_supplierForest_actual_100339
  · exact g32p_supplierForest_actual_100383
  · exact g32p_supplierForest_actual_100386
  · exact g32p_supplierForest_actual_100459
  · exact g32p_supplierForest_actual_100474
  · exact g32p_supplierForest_actual_100490
  · exact g32p_supplierForest_actual_100507
  · exact g32p_supplierForest_actual_100530
  · exact g32p_supplierForest_actual_100553
  · exact g32p_supplierForest_actual_100564
  · exact g32p_supplierForest_actual_100566
  · exact g32p_supplierForest_actual_100574
  · exact g32p_supplierForest_actual_100600
  · exact g32p_supplierForest_actual_100665
  · exact g32p_supplierForest_actual_100690
  · exact g32p_supplierForest_actual_100694
  · exact g32p_supplierForest_actual_100719
  · exact g32p_supplierForest_actual_100812
  · exact g32p_supplierForest_actual_100824
  · exact g32p_supplierForest_actual_100849
  · exact g32p_supplierForest_actual_100855
  · exact g32p_supplierForest_actual_100895
  · exact g32p_supplierForest_actual_100901
  · exact g32p_supplierForest_actual_100932
  · exact g32p_supplierForest_actual_100944
  · exact g32p_supplierForest_actual_100950
  · exact g32p_supplierForest_actual_100978
  · exact g32p_supplierForest_actual_101009
  · exact g32p_supplierForest_actual_101016
  · exact g32p_supplierForest_actual_101024
  · exact g32p_supplierForest_actual_101027
  · exact g32p_supplierForest_actual_101060
  · exact g32p_supplierForest_actual_101076
  · exact g32p_supplierForest_actual_101095
  · exact g32p_supplierForest_actual_101133
  · exact g32p_supplierForest_actual_101145
  · exact g32p_supplierForest_actual_101159
  · exact g32p_supplierForest_actual_101160
  · exact g32p_supplierForest_actual_101185
  · exact g32p_supplierForest_actual_101196
  · exact g32p_supplierForest_actual_101208
  · exact g32p_supplierForest_actual_101214
  · exact g32p_supplierForest_actual_101225
  · exact g32p_supplierForest_actual_101245
  · exact g32p_supplierForest_actual_101250
  · exact g32p_supplierForest_actual_101264
  · exact g32p_supplierForest_actual_101275
  · exact g32p_supplierForest_actual_101283
  · exact g32p_supplierForest_actual_101316
  · exact g32p_supplierForest_actual_101342
  · exact g32p_supplierForest_actual_101344
  · exact g32p_supplierForest_actual_101360
  · exact g32p_supplierForest_actual_101371
  · exact g32p_supplierForest_actual_101386
  · exact g32p_supplierForest_actual_101396
  · exact g32p_supplierForest_actual_101397
  · exact g32p_supplierForest_actual_101427
  · exact g32p_supplierForest_actual_101429
  · exact g32p_supplierForest_actual_101442
  · exact g32p_supplierForest_actual_101451
  · exact g32p_supplierForest_actual_101469
  · exact g32p_supplierForest_actual_101471
  · exact g32p_supplierForest_actual_101499
  · exact g32p_supplierForest_actual_101523
  · exact g32p_supplierForest_actual_101572
  · exact g32p_supplierForest_actual_101582
  · exact g32p_supplierForest_actual_101589
  · exact g32p_supplierForest_actual_101604
  · exact g32p_supplierForest_actual_101611
  · exact g32p_supplierForest_actual_101655
  · exact g32p_supplierForest_actual_101672
  · exact g32p_supplierForest_actual_101677
  · exact g32p_supplierForest_actual_101698
  · exact g32p_supplierForest_actual_101703
  · exact g32p_supplierForest_actual_101716
  · exact g32p_supplierForest_actual_101717
  · exact g32p_supplierForest_actual_101726
  · exact g32p_supplierForest_actual_101729
  · exact g32p_supplierForest_actual_101747
  · exact g32p_supplierForest_actual_101777
  · exact g32p_supplierForest_actual_101805
  · exact g32p_supplierForest_actual_101835
  · exact g32p_supplierForest_actual_101841
  · exact g32p_supplierForest_actual_101863
  · exact g32p_supplierForest_actual_101874
  · exact g32p_supplierForest_actual_101878
  · exact g32p_supplierForest_actual_101895
  · exact g32p_supplierForest_actual_101900
  · exact g32p_supplierForest_actual_101933
  · exact g32p_supplierForest_actual_101950
  · exact g32p_supplierForest_actual_101951
  · exact g32p_supplierForest_actual_101993
  · exact g32p_supplierForest_actual_102023
  · exact g32p_supplierForest_actual_102030
  · exact g32p_supplierForest_actual_102042
  · exact g32p_supplierForest_actual_102053
  · exact g32p_supplierForest_actual_102065
  · exact g32p_supplierForest_actual_102115
  · exact g32p_supplierForest_actual_102127
  · exact g32p_supplierForest_actual_102135
  · exact g32p_supplierForest_actual_102148
  · exact g32p_supplierForest_actual_102154
  · exact g32p_supplierForest_actual_102161
  · exact g32p_supplierForest_actual_102194
  · exact g32p_supplierForest_actual_102205
  · exact g32p_supplierForest_actual_102224
  · exact g32p_supplierForest_actual_102241
  · exact g32p_supplierForest_actual_102244
  · exact g32p_supplierForest_actual_102250
  · exact g32p_supplierForest_actual_102282
  · exact g32p_supplierForest_actual_102284
  · exact g32p_supplierForest_actual_102310
  · exact g32p_supplierForest_actual_102317
  · exact g32p_supplierForest_actual_102386
  · exact g32p_supplierForest_actual_102411
  · exact g32p_supplierForest_actual_102412
  · exact g32p_supplierForest_actual_102416
  · exact g32p_supplierForest_actual_102498
  · exact g32p_supplierForest_actual_102503
  · exact g32p_supplierForest_actual_102504
  · exact g32p_supplierForest_actual_102521
  · exact g32p_supplierForest_actual_102537
  · exact g32p_supplierForest_actual_102551
  · exact g32p_supplierForest_actual_102552
  · exact g32p_supplierForest_actual_102597
  · exact g32p_supplierForest_actual_102614
  · exact g32p_supplierForest_actual_102619
  · exact g32p_supplierForest_actual_102629
  · exact g32p_supplierForest_actual_102640
  · exact g32p_supplierForest_actual_102656
  · exact g32p_supplierForest_actual_102682
  · exact g32p_supplierForest_actual_102687
  · exact g32p_supplierForest_actual_102697
  · exact g32p_supplierForest_actual_102707
  · exact g32p_supplierForest_actual_102718
  · exact g32p_supplierForest_actual_102741
  · exact g32p_supplierForest_actual_102764
  · exact g32p_supplierForest_actual_102786
  · exact g32p_supplierForest_actual_102842
  · exact g32p_supplierForest_actual_102843
  · exact g32p_supplierForest_actual_102858
  · exact g32p_supplierForest_actual_102861
  · exact g32p_supplierForest_actual_102873
  · exact g32p_supplierForest_actual_102893
  · exact g32p_supplierForest_actual_102927
  · exact g32p_supplierForest_actual_102943
  · exact g32p_supplierForest_actual_102985
  · exact g32p_supplierForest_actual_103013
  · exact g32p_supplierForest_actual_103014
  · exact g32p_supplierForest_actual_103020
  · exact g32p_supplierForest_actual_103034
  · exact g32p_supplierForest_actual_103043
  · exact g32p_supplierForest_actual_103087
  · exact g32p_supplierForest_actual_103105
  · exact g32p_supplierForest_actual_103121
  · exact g32p_supplierForest_actual_103170
  · exact g32p_supplierForest_actual_103203
  · exact g32p_supplierForest_actual_103227
  · exact g32p_supplierForest_actual_103239
  · exact g32p_supplierForest_actual_103244
  · exact g32p_supplierForest_actual_103257
  · exact g32p_supplierForest_actual_103260
  · exact g32p_supplierForest_actual_103306
  · exact g32p_supplierForest_actual_103340
  · exact g32p_supplierForest_actual_103365
  · exact g32p_supplierForest_actual_103385
  · exact g32p_supplierForest_actual_103400
  · exact g32p_supplierForest_actual_103422
  · exact g32p_supplierForest_actual_103435
  · exact g32p_supplierForest_actual_103438
  · exact g32p_supplierForest_actual_103439
  · exact g32p_supplierForest_actual_103452
  · exact g32p_supplierForest_actual_103532
  · exact g32p_supplierForest_actual_103545
  · exact g32p_supplierForest_actual_103560
  · exact g32p_supplierForest_actual_103612
  · exact g32p_supplierForest_actual_103644
  · exact g32p_supplierForest_actual_103647
  · exact g32p_supplierForest_actual_103655
  · exact g32p_supplierForest_actual_103667
  · exact g32p_supplierForest_actual_103678
  · exact g32p_supplierForest_actual_103685
  · exact g32p_supplierForest_actual_103703
  · exact g32p_supplierForest_actual_103723
  · exact g32p_supplierForest_actual_103805
  · exact g32p_supplierForest_actual_103836
  · exact g32p_supplierForest_actual_103861
  · exact g32p_supplierForest_actual_103868
  · exact g32p_supplierForest_actual_103878
  · exact g32p_supplierForest_actual_103882
  · exact g32p_supplierForest_actual_103891
  · exact g32p_supplierForest_actual_103901
  · exact g32p_supplierForest_actual_103964
  · exact g32p_supplierForest_actual_103979
  · exact g32p_supplierForest_actual_104038
  · exact g32p_supplierForest_actual_104054
  · exact g32p_supplierForest_actual_104069
  · exact g32p_supplierForest_actual_104100
  · exact g32p_supplierForest_actual_104156
  · exact g32p_supplierForest_actual_104160
  · exact g32p_supplierForest_actual_104194
  · exact g32p_supplierForest_actual_104198
  · exact g32p_supplierForest_actual_104221
  · exact g32p_supplierForest_actual_104236
  · exact g32p_supplierForest_actual_104243
  · exact g32p_supplierForest_actual_104245
  · exact g32p_supplierForest_actual_104247
  · exact g32p_supplierForest_actual_104261
  · exact g32p_supplierForest_actual_104268
  · exact g32p_supplierForest_actual_104269
  · exact g32p_supplierForest_actual_104308
  · exact g32p_supplierForest_actual_104329
  · exact g32p_supplierForest_actual_104343
  · exact g32p_supplierForest_actual_104344
  · exact g32p_supplierForest_actual_104364
  · exact g32p_supplierForest_actual_104365
  · exact g32p_supplierForest_actual_104407
  · exact g32p_supplierForest_actual_104434
  · exact g32p_supplierForest_actual_104438

def g32p_supplierForest_nodes_103 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_104452 else g32p_supplierForest_node_104472) else (if i.val < 3 then g32p_supplierForest_node_104475 else g32p_supplierForest_node_104477)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_104479 else g32p_supplierForest_node_104516) else (if i.val < 7 then g32p_supplierForest_node_104521 else g32p_supplierForest_node_104523))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_104531 else g32p_supplierForest_node_104543) else (if i.val < 11 then g32p_supplierForest_node_104558 else g32p_supplierForest_node_104568)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_104594 else g32p_supplierForest_node_104611) else (if i.val < 15 then g32p_supplierForest_node_104619 else g32p_supplierForest_node_104640)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_104662 else g32p_supplierForest_node_104663) else (if i.val < 19 then g32p_supplierForest_node_104685 else g32p_supplierForest_node_104741)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_104770 else g32p_supplierForest_node_104776) else (if i.val < 23 then g32p_supplierForest_node_104782 else g32p_supplierForest_node_104820))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_104832 else g32p_supplierForest_node_104924) else (if i.val < 27 then g32p_supplierForest_node_104949 else g32p_supplierForest_node_104971)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_105017 else g32p_supplierForest_node_105019) else (if i.val < 31 then g32p_supplierForest_node_105031 else g32p_supplierForest_node_105036))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_105063 else g32p_supplierForest_node_105072) else (if i.val < 35 then g32p_supplierForest_node_105080 else g32p_supplierForest_node_105084)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_105095 else g32p_supplierForest_node_105130) else (if i.val < 39 then g32p_supplierForest_node_105143 else g32p_supplierForest_node_105188))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_105207 else g32p_supplierForest_node_105208) else (if i.val < 43 then g32p_supplierForest_node_105242 else g32p_supplierForest_node_105244)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_105253 else g32p_supplierForest_node_105264) else (if i.val < 47 then g32p_supplierForest_node_105286 else g32p_supplierForest_node_105335)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_105344 else g32p_supplierForest_node_105367) else (if i.val < 51 then g32p_supplierForest_node_105369 else g32p_supplierForest_node_105390)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_105393 else g32p_supplierForest_node_105395) else (if i.val < 55 then g32p_supplierForest_node_105397 else g32p_supplierForest_node_105460))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_105481 else g32p_supplierForest_node_105499) else (if i.val < 59 then g32p_supplierForest_node_105531 else g32p_supplierForest_node_105551)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_105564 else g32p_supplierForest_node_105604) else (if i.val < 63 then g32p_supplierForest_node_105618 else g32p_supplierForest_node_105676)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_105684 else g32p_supplierForest_node_105714) else (if i.val < 67 then g32p_supplierForest_node_105733 else g32p_supplierForest_node_105750)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_105755 else g32p_supplierForest_node_105766) else (if i.val < 71 then g32p_supplierForest_node_105783 else g32p_supplierForest_node_105798))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_105799 else g32p_supplierForest_node_105803) else (if i.val < 75 then g32p_supplierForest_node_105828 else g32p_supplierForest_node_105842)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_105872 else g32p_supplierForest_node_105879) else (if i.val < 79 then g32p_supplierForest_node_105891 else g32p_supplierForest_node_105901)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_105920 else g32p_supplierForest_node_105925) else (if i.val < 83 then g32p_supplierForest_node_105948 else g32p_supplierForest_node_105973)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_106029 else g32p_supplierForest_node_106032) else (if i.val < 87 then g32p_supplierForest_node_106043 else g32p_supplierForest_node_106047))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_106053 else g32p_supplierForest_node_106057) else (if i.val < 91 then g32p_supplierForest_node_106081 else g32p_supplierForest_node_106116)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_106142 else g32p_supplierForest_node_106179) else (if i.val < 95 then g32p_supplierForest_node_106219 else g32p_supplierForest_node_106225))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_106256 else g32p_supplierForest_node_106285) else (if i.val < 99 then g32p_supplierForest_node_106288 else g32p_supplierForest_node_106299)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_106339 else g32p_supplierForest_node_106363) else (if i.val < 103 then g32p_supplierForest_node_106372 else g32p_supplierForest_node_106381))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_106387 else g32p_supplierForest_node_106390) else (if i.val < 107 then g32p_supplierForest_node_106394 else g32p_supplierForest_node_106397)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_106402 else g32p_supplierForest_node_106404) else (if i.val < 111 then g32p_supplierForest_node_106442 else g32p_supplierForest_node_106455)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_106465 else g32p_supplierForest_node_106469) else (if i.val < 115 then g32p_supplierForest_node_106477 else g32p_supplierForest_node_106480)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_106487 else g32p_supplierForest_node_106541) else (if i.val < 119 then g32p_supplierForest_node_106618 else g32p_supplierForest_node_106623))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_106634 else g32p_supplierForest_node_106691) else (if i.val < 123 then g32p_supplierForest_node_106701 else g32p_supplierForest_node_106705)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_106738 else g32p_supplierForest_node_106746) else (if i.val < 127 then g32p_supplierForest_node_106773 else g32p_supplierForest_node_106818))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_106822 else g32p_supplierForest_node_106861) else (if i.val < 131 then g32p_supplierForest_node_106869 else g32p_supplierForest_node_106874)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_106893 else g32p_supplierForest_node_106907) else (if i.val < 135 then g32p_supplierForest_node_106958 else g32p_supplierForest_node_106979))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_106994 else g32p_supplierForest_node_107039) else (if i.val < 139 then g32p_supplierForest_node_107072 else g32p_supplierForest_node_107092)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_107100 else g32p_supplierForest_node_107122) else (if i.val < 143 then g32p_supplierForest_node_107131 else g32p_supplierForest_node_107160)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_107174 else g32p_supplierForest_node_107175) else (if i.val < 147 then g32p_supplierForest_node_107203 else g32p_supplierForest_node_107234)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_107262 else g32p_supplierForest_node_107271) else (if i.val < 151 then g32p_supplierForest_node_107292 else g32p_supplierForest_node_107338))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_107407 else g32p_supplierForest_node_107415) else (if i.val < 155 then g32p_supplierForest_node_107432 else g32p_supplierForest_node_107515)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_107559 else g32p_supplierForest_node_107584) else (if i.val < 159 then g32p_supplierForest_node_107692 else g32p_supplierForest_node_107697))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_107754 else g32p_supplierForest_node_107766) else (if i.val < 163 then g32p_supplierForest_node_107785 else g32p_supplierForest_node_107805)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_107884 else g32p_supplierForest_node_107923) else (if i.val < 167 then g32p_supplierForest_node_107934 else g32p_supplierForest_node_107956))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_107982 else g32p_supplierForest_node_107985) else (if i.val < 171 then g32p_supplierForest_node_107997 else g32p_supplierForest_node_107998)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_108000 else g32p_supplierForest_node_108011) else (if i.val < 175 then g32p_supplierForest_node_108041 else g32p_supplierForest_node_108052)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_108057 else g32p_supplierForest_node_108078) else (if i.val < 179 then g32p_supplierForest_node_108092 else g32p_supplierForest_node_108093)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_108098 else g32p_supplierForest_node_108102) else (if i.val < 183 then g32p_supplierForest_node_108112 else g32p_supplierForest_node_108113))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_108116 else g32p_supplierForest_node_108118) else (if i.val < 187 then g32p_supplierForest_node_108131 else g32p_supplierForest_node_108138)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_108146 else g32p_supplierForest_node_108161) else (if i.val < 191 then g32p_supplierForest_node_108183 else g32p_supplierForest_node_108191)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_108205 else g32p_supplierForest_node_108230) else (if i.val < 195 then g32p_supplierForest_node_108248 else g32p_supplierForest_node_108300)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_108315 else g32p_supplierForest_node_108340) else (if i.val < 199 then g32p_supplierForest_node_108348 else g32p_supplierForest_node_108367))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_108369 else g32p_supplierForest_node_108374) else (if i.val < 203 then g32p_supplierForest_node_108397 else g32p_supplierForest_node_108425)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_108473 else g32p_supplierForest_node_108477) else (if i.val < 207 then g32p_supplierForest_node_108556 else g32p_supplierForest_node_108595)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_108601 else g32p_supplierForest_node_108625) else (if i.val < 211 then g32p_supplierForest_node_108627 else g32p_supplierForest_node_108647)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_108653 else g32p_supplierForest_node_108657) else (if i.val < 215 then g32p_supplierForest_node_108660 else g32p_supplierForest_node_108679))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_108680 else g32p_supplierForest_node_108686) else (if i.val < 219 then g32p_supplierForest_node_108699 else g32p_supplierForest_node_108762)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_108784 else g32p_supplierForest_node_108810) else (if i.val < 223 then g32p_supplierForest_node_108811 else g32p_supplierForest_node_108819))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_108876 else g32p_supplierForest_node_108877) else (if i.val < 227 then g32p_supplierForest_node_108878 else g32p_supplierForest_node_108897)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_108913 else g32p_supplierForest_node_108936) else (if i.val < 231 then g32p_supplierForest_node_108959 else g32p_supplierForest_node_108985))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_108989 else g32p_supplierForest_node_108998) else (if i.val < 235 then g32p_supplierForest_node_108999 else g32p_supplierForest_node_109002)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_109037 else g32p_supplierForest_node_109076) else (if i.val < 239 then g32p_supplierForest_node_109105 else g32p_supplierForest_node_109135)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_109140 else g32p_supplierForest_node_109155) else (if i.val < 243 then g32p_supplierForest_node_109167 else g32p_supplierForest_node_109169)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_109242 else g32p_supplierForest_node_109248) else (if i.val < 247 then g32p_supplierForest_node_109262 else g32p_supplierForest_node_109304))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_109322 else g32p_supplierForest_node_109331) else (if i.val < 251 then g32p_supplierForest_node_109358 else g32p_supplierForest_node_109393)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_109415 else g32p_supplierForest_node_109428) else (if i.val < 255 then g32p_supplierForest_node_109509 else g32p_supplierForest_node_109534))))))))

def g32p_supplierForest_classes_103 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 30 else 16) else (if i.val < 3 then 16 else 57)) else (if i.val < 6 then (if i.val < 5 then 30 else 15) else (if i.val < 7 then 33 else 33))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 57 else 30) else (if i.val < 11 then 29 else 57)) else (if i.val < 14 then (if i.val < 13 then 59 else 30) else (if i.val < 15 then 63 else 59)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 57 else 60) else (if i.val < 19 then 57 else 30)) else (if i.val < 22 then (if i.val < 21 then 57 else 60) else (if i.val < 23 then 60 else 29))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 17 else 33) else (if i.val < 27 then 29 else 58)) else (if i.val < 30 then (if i.val < 29 then 17 else 30) else (if i.val < 31 then 60 else 30))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 60 else 29) else (if i.val < 35 then 57 else 36)) else (if i.val < 38 then (if i.val < 37 then 14 else 57) else (if i.val < 39 then 57 else 29))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 60 else 60) else (if i.val < 43 then 66 else 57)) else (if i.val < 46 then (if i.val < 45 then 60 else 59) else (if i.val < 47 then 34 else 60)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 57 else 15) else (if i.val < 51 then 58 else 61)) else (if i.val < 54 then (if i.val < 53 then 35 else 30) else (if i.val < 55 then 29 else 59))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 15) else (if i.val < 59 then 30 else 29)) else (if i.val < 62 then (if i.val < 61 then 30 else 60) else (if i.val < 63 then 30 else 60)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 57 else 33) else (if i.val < 67 then 29 else 15)) else (if i.val < 70 then (if i.val < 69 then 66 else 62) else (if i.val < 71 then 30 else 57))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 63 else 57) else (if i.val < 75 then 58 else 15)) else (if i.val < 78 then (if i.val < 77 then 57 else 29) else (if i.val < 79 then 63 else 16)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 57 else 66) else (if i.val < 83 then 57 else 34)) else (if i.val < 86 then (if i.val < 85 then 30 else 58) else (if i.val < 87 then 29 else 30))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 60 else 30) else (if i.val < 91 then 29 else 57)) else (if i.val < 94 then (if i.val < 93 then 14 else 60) else (if i.val < 95 then 29 else 30))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 60 else 30) else (if i.val < 99 then 60 else 29)) else (if i.val < 102 then (if i.val < 101 then 16 else 57) else (if i.val < 103 then 30 else 59))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 60 else 29) else (if i.val < 107 then 29 else 60)) else (if i.val < 110 then (if i.val < 109 then 66 else 57) else (if i.val < 111 then 34 else 29)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 57 else 58) else (if i.val < 115 then 33 else 57)) else (if i.val < 118 then (if i.val < 117 then 59 else 35) else (if i.val < 119 then 34 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 29 else 30) else (if i.val < 123 then 66 else 36)) else (if i.val < 126 then (if i.val < 125 then 32 else 30) else (if i.val < 127 then 30 else 30))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 30 else 57) else (if i.val < 131 then 90 else 30)) else (if i.val < 134 then (if i.val < 133 then 33 else 30) else (if i.val < 135 then 60 else 17))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 60 else 36) else (if i.val < 139 then 60 else 90)) else (if i.val < 142 then (if i.val < 141 then 17 else 59) else (if i.val < 143 then 59 else 57)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 57 else 14) else (if i.val < 147 then 60 else 57)) else (if i.val < 150 then (if i.val < 149 then 63 else 61) else (if i.val < 151 then 29 else 29))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 30 else 63) else (if i.val < 155 then 29 else 16)) else (if i.val < 158 then (if i.val < 157 then 59 else 30) else (if i.val < 159 then 36 else 57))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 60 else 90) else (if i.val < 163 then 57 else 29)) else (if i.val < 166 then (if i.val < 165 then 66 else 29) else (if i.val < 167 then 63 else 63))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 60 else 57) else (if i.val < 171 then 59 else 90)) else (if i.val < 174 then (if i.val < 173 then 63 else 30) else (if i.val < 175 then 16 else 64)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 36 else 57) else (if i.val < 179 then 57 else 16)) else (if i.val < 182 then (if i.val < 181 then 63 else 16) else (if i.val < 183 then 30 else 60))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 36 else 30) else (if i.val < 187 then 57 else 57)) else (if i.val < 190 then (if i.val < 189 then 31 else 57) else (if i.val < 191 then 63 else 62)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 30 else 36) else (if i.val < 195 then 91 else 34)) else (if i.val < 198 then (if i.val < 197 then 57 else 16) else (if i.val < 199 then 63 else 60))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 60 else 66) else (if i.val < 203 then 30 else 57)) else (if i.val < 206 then (if i.val < 205 then 17 else 30) else (if i.val < 207 then 57 else 30)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 33 else 60) else (if i.val < 211 then 30 else 66)) else (if i.val < 214 then (if i.val < 213 then 16 else 63) else (if i.val < 215 then 32 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 60 else 60) else (if i.val < 219 then 62 else 34)) else (if i.val < 222 then (if i.val < 221 then 30 else 66) else (if i.val < 223 then 62 else 64))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 30 else 57) else (if i.val < 227 then 57 else 36)) else (if i.val < 230 then (if i.val < 229 then 16 else 16) else (if i.val < 231 then 57 else 30))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 57 else 30) else (if i.val < 235 then 57 else 29)) else (if i.val < 238 then (if i.val < 237 then 57 else 34) else (if i.val < 239 then 57 else 59)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 59 else 16) else (if i.val < 243 then 60 else 57)) else (if i.val < 246 then (if i.val < 245 then 15 else 59) else (if i.val < 247 then 16 else 29))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 30 else 29) else (if i.val < 251 then 16 else 30)) else (if i.val < 254 then (if i.val < 253 then 57 else 61) else (if i.val < 255 then 29 else 30))))))))

theorem g32p_supplierForest_actual_103 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_103 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_103 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_104452
  · exact g32p_supplierForest_actual_104472
  · exact g32p_supplierForest_actual_104475
  · exact g32p_supplierForest_actual_104477
  · exact g32p_supplierForest_actual_104479
  · exact g32p_supplierForest_actual_104516
  · exact g32p_supplierForest_actual_104521
  · exact g32p_supplierForest_actual_104523
  · exact g32p_supplierForest_actual_104531
  · exact g32p_supplierForest_actual_104543
  · exact g32p_supplierForest_actual_104558
  · exact g32p_supplierForest_actual_104568
  · exact g32p_supplierForest_actual_104594
  · exact g32p_supplierForest_actual_104611
  · exact g32p_supplierForest_actual_104619
  · exact g32p_supplierForest_actual_104640
  · exact g32p_supplierForest_actual_104662
  · exact g32p_supplierForest_actual_104663
  · exact g32p_supplierForest_actual_104685
  · exact g32p_supplierForest_actual_104741
  · exact g32p_supplierForest_actual_104770
  · exact g32p_supplierForest_actual_104776
  · exact g32p_supplierForest_actual_104782
  · exact g32p_supplierForest_actual_104820
  · exact g32p_supplierForest_actual_104832
  · exact g32p_supplierForest_actual_104924
  · exact g32p_supplierForest_actual_104949
  · exact g32p_supplierForest_actual_104971
  · exact g32p_supplierForest_actual_105017
  · exact g32p_supplierForest_actual_105019
  · exact g32p_supplierForest_actual_105031
  · exact g32p_supplierForest_actual_105036
  · exact g32p_supplierForest_actual_105063
  · exact g32p_supplierForest_actual_105072
  · exact g32p_supplierForest_actual_105080
  · exact g32p_supplierForest_actual_105084
  · exact g32p_supplierForest_actual_105095
  · exact g32p_supplierForest_actual_105130
  · exact g32p_supplierForest_actual_105143
  · exact g32p_supplierForest_actual_105188
  · exact g32p_supplierForest_actual_105207
  · exact g32p_supplierForest_actual_105208
  · exact g32p_supplierForest_actual_105242
  · exact g32p_supplierForest_actual_105244
  · exact g32p_supplierForest_actual_105253
  · exact g32p_supplierForest_actual_105264
  · exact g32p_supplierForest_actual_105286
  · exact g32p_supplierForest_actual_105335
  · exact g32p_supplierForest_actual_105344
  · exact g32p_supplierForest_actual_105367
  · exact g32p_supplierForest_actual_105369
  · exact g32p_supplierForest_actual_105390
  · exact g32p_supplierForest_actual_105393
  · exact g32p_supplierForest_actual_105395
  · exact g32p_supplierForest_actual_105397
  · exact g32p_supplierForest_actual_105460
  · exact g32p_supplierForest_actual_105481
  · exact g32p_supplierForest_actual_105499
  · exact g32p_supplierForest_actual_105531
  · exact g32p_supplierForest_actual_105551
  · exact g32p_supplierForest_actual_105564
  · exact g32p_supplierForest_actual_105604
  · exact g32p_supplierForest_actual_105618
  · exact g32p_supplierForest_actual_105676
  · exact g32p_supplierForest_actual_105684
  · exact g32p_supplierForest_actual_105714
  · exact g32p_supplierForest_actual_105733
  · exact g32p_supplierForest_actual_105750
  · exact g32p_supplierForest_actual_105755
  · exact g32p_supplierForest_actual_105766
  · exact g32p_supplierForest_actual_105783
  · exact g32p_supplierForest_actual_105798
  · exact g32p_supplierForest_actual_105799
  · exact g32p_supplierForest_actual_105803
  · exact g32p_supplierForest_actual_105828
  · exact g32p_supplierForest_actual_105842
  · exact g32p_supplierForest_actual_105872
  · exact g32p_supplierForest_actual_105879
  · exact g32p_supplierForest_actual_105891
  · exact g32p_supplierForest_actual_105901
  · exact g32p_supplierForest_actual_105920
  · exact g32p_supplierForest_actual_105925
  · exact g32p_supplierForest_actual_105948
  · exact g32p_supplierForest_actual_105973
  · exact g32p_supplierForest_actual_106029
  · exact g32p_supplierForest_actual_106032
  · exact g32p_supplierForest_actual_106043
  · exact g32p_supplierForest_actual_106047
  · exact g32p_supplierForest_actual_106053
  · exact g32p_supplierForest_actual_106057
  · exact g32p_supplierForest_actual_106081
  · exact g32p_supplierForest_actual_106116
  · exact g32p_supplierForest_actual_106142
  · exact g32p_supplierForest_actual_106179
  · exact g32p_supplierForest_actual_106219
  · exact g32p_supplierForest_actual_106225
  · exact g32p_supplierForest_actual_106256
  · exact g32p_supplierForest_actual_106285
  · exact g32p_supplierForest_actual_106288
  · exact g32p_supplierForest_actual_106299
  · exact g32p_supplierForest_actual_106339
  · exact g32p_supplierForest_actual_106363
  · exact g32p_supplierForest_actual_106372
  · exact g32p_supplierForest_actual_106381
  · exact g32p_supplierForest_actual_106387
  · exact g32p_supplierForest_actual_106390
  · exact g32p_supplierForest_actual_106394
  · exact g32p_supplierForest_actual_106397
  · exact g32p_supplierForest_actual_106402
  · exact g32p_supplierForest_actual_106404
  · exact g32p_supplierForest_actual_106442
  · exact g32p_supplierForest_actual_106455
  · exact g32p_supplierForest_actual_106465
  · exact g32p_supplierForest_actual_106469
  · exact g32p_supplierForest_actual_106477
  · exact g32p_supplierForest_actual_106480
  · exact g32p_supplierForest_actual_106487
  · exact g32p_supplierForest_actual_106541
  · exact g32p_supplierForest_actual_106618
  · exact g32p_supplierForest_actual_106623
  · exact g32p_supplierForest_actual_106634
  · exact g32p_supplierForest_actual_106691
  · exact g32p_supplierForest_actual_106701
  · exact g32p_supplierForest_actual_106705
  · exact g32p_supplierForest_actual_106738
  · exact g32p_supplierForest_actual_106746
  · exact g32p_supplierForest_actual_106773
  · exact g32p_supplierForest_actual_106818
  · exact g32p_supplierForest_actual_106822
  · exact g32p_supplierForest_actual_106861
  · exact g32p_supplierForest_actual_106869
  · exact g32p_supplierForest_actual_106874
  · exact g32p_supplierForest_actual_106893
  · exact g32p_supplierForest_actual_106907
  · exact g32p_supplierForest_actual_106958
  · exact g32p_supplierForest_actual_106979
  · exact g32p_supplierForest_actual_106994
  · exact g32p_supplierForest_actual_107039
  · exact g32p_supplierForest_actual_107072
  · exact g32p_supplierForest_actual_107092
  · exact g32p_supplierForest_actual_107100
  · exact g32p_supplierForest_actual_107122
  · exact g32p_supplierForest_actual_107131
  · exact g32p_supplierForest_actual_107160
  · exact g32p_supplierForest_actual_107174
  · exact g32p_supplierForest_actual_107175
  · exact g32p_supplierForest_actual_107203
  · exact g32p_supplierForest_actual_107234
  · exact g32p_supplierForest_actual_107262
  · exact g32p_supplierForest_actual_107271
  · exact g32p_supplierForest_actual_107292
  · exact g32p_supplierForest_actual_107338
  · exact g32p_supplierForest_actual_107407
  · exact g32p_supplierForest_actual_107415
  · exact g32p_supplierForest_actual_107432
  · exact g32p_supplierForest_actual_107515
  · exact g32p_supplierForest_actual_107559
  · exact g32p_supplierForest_actual_107584
  · exact g32p_supplierForest_actual_107692
  · exact g32p_supplierForest_actual_107697
  · exact g32p_supplierForest_actual_107754
  · exact g32p_supplierForest_actual_107766
  · exact g32p_supplierForest_actual_107785
  · exact g32p_supplierForest_actual_107805
  · exact g32p_supplierForest_actual_107884
  · exact g32p_supplierForest_actual_107923
  · exact g32p_supplierForest_actual_107934
  · exact g32p_supplierForest_actual_107956
  · exact g32p_supplierForest_actual_107982
  · exact g32p_supplierForest_actual_107985
  · exact g32p_supplierForest_actual_107997
  · exact g32p_supplierForest_actual_107998
  · exact g32p_supplierForest_actual_108000
  · exact g32p_supplierForest_actual_108011
  · exact g32p_supplierForest_actual_108041
  · exact g32p_supplierForest_actual_108052
  · exact g32p_supplierForest_actual_108057
  · exact g32p_supplierForest_actual_108078
  · exact g32p_supplierForest_actual_108092
  · exact g32p_supplierForest_actual_108093
  · exact g32p_supplierForest_actual_108098
  · exact g32p_supplierForest_actual_108102
  · exact g32p_supplierForest_actual_108112
  · exact g32p_supplierForest_actual_108113
  · exact g32p_supplierForest_actual_108116
  · exact g32p_supplierForest_actual_108118
  · exact g32p_supplierForest_actual_108131
  · exact g32p_supplierForest_actual_108138
  · exact g32p_supplierForest_actual_108146
  · exact g32p_supplierForest_actual_108161
  · exact g32p_supplierForest_actual_108183
  · exact g32p_supplierForest_actual_108191
  · exact g32p_supplierForest_actual_108205
  · exact g32p_supplierForest_actual_108230
  · exact g32p_supplierForest_actual_108248
  · exact g32p_supplierForest_actual_108300
  · exact g32p_supplierForest_actual_108315
  · exact g32p_supplierForest_actual_108340
  · exact g32p_supplierForest_actual_108348
  · exact g32p_supplierForest_actual_108367
  · exact g32p_supplierForest_actual_108369
  · exact g32p_supplierForest_actual_108374
  · exact g32p_supplierForest_actual_108397
  · exact g32p_supplierForest_actual_108425
  · exact g32p_supplierForest_actual_108473
  · exact g32p_supplierForest_actual_108477
  · exact g32p_supplierForest_actual_108556
  · exact g32p_supplierForest_actual_108595
  · exact g32p_supplierForest_actual_108601
  · exact g32p_supplierForest_actual_108625
  · exact g32p_supplierForest_actual_108627
  · exact g32p_supplierForest_actual_108647
  · exact g32p_supplierForest_actual_108653
  · exact g32p_supplierForest_actual_108657
  · exact g32p_supplierForest_actual_108660
  · exact g32p_supplierForest_actual_108679
  · exact g32p_supplierForest_actual_108680
  · exact g32p_supplierForest_actual_108686
  · exact g32p_supplierForest_actual_108699
  · exact g32p_supplierForest_actual_108762
  · exact g32p_supplierForest_actual_108784
  · exact g32p_supplierForest_actual_108810
  · exact g32p_supplierForest_actual_108811
  · exact g32p_supplierForest_actual_108819
  · exact g32p_supplierForest_actual_108876
  · exact g32p_supplierForest_actual_108877
  · exact g32p_supplierForest_actual_108878
  · exact g32p_supplierForest_actual_108897
  · exact g32p_supplierForest_actual_108913
  · exact g32p_supplierForest_actual_108936
  · exact g32p_supplierForest_actual_108959
  · exact g32p_supplierForest_actual_108985
  · exact g32p_supplierForest_actual_108989
  · exact g32p_supplierForest_actual_108998
  · exact g32p_supplierForest_actual_108999
  · exact g32p_supplierForest_actual_109002
  · exact g32p_supplierForest_actual_109037
  · exact g32p_supplierForest_actual_109076
  · exact g32p_supplierForest_actual_109105
  · exact g32p_supplierForest_actual_109135
  · exact g32p_supplierForest_actual_109140
  · exact g32p_supplierForest_actual_109155
  · exact g32p_supplierForest_actual_109167
  · exact g32p_supplierForest_actual_109169
  · exact g32p_supplierForest_actual_109242
  · exact g32p_supplierForest_actual_109248
  · exact g32p_supplierForest_actual_109262
  · exact g32p_supplierForest_actual_109304
  · exact g32p_supplierForest_actual_109322
  · exact g32p_supplierForest_actual_109331
  · exact g32p_supplierForest_actual_109358
  · exact g32p_supplierForest_actual_109393
  · exact g32p_supplierForest_actual_109415
  · exact g32p_supplierForest_actual_109428
  · exact g32p_supplierForest_actual_109509
  · exact g32p_supplierForest_actual_109534

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_109537 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109537 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109537 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114655 := by
  decide +kernel

theorem g32p_supplierForest_actual_109537 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109537) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_109537
    g32p_supplierForest_actual_114655

def g32p_supplierForest_node_109576 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109576 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109576 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_108925 := by
  decide +kernel

theorem g32p_supplierForest_actual_109576 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109576) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_109576
    g32p_supplierForest_actual_108925

def g32p_supplierForest_node_109618 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_109618 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109618 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104076 := by
  decide +kernel

theorem g32p_supplierForest_actual_109618 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109618) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_109618
    g32p_supplierForest_actual_104076

def g32p_supplierForest_node_109653 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109653 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109653 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026868 := by
  decide +kernel

theorem g32p_supplierForest_actual_109653 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109653) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_109653
    g32p_supplierForest_actual_026868

def g32p_supplierForest_node_109687 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_109687 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109687 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_107260 := by
  decide +kernel

theorem g32p_supplierForest_actual_109687 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109687) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_109687
    g32p_supplierForest_actual_107260

def g32p_supplierForest_node_109709 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109709 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109709 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103744 := by
  decide +kernel

theorem g32p_supplierForest_actual_109709 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109709) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_109709
    g32p_supplierForest_actual_103744

def g32p_supplierForest_node_109715 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109715 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109715 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_107816 := by
  decide +kernel

theorem g32p_supplierForest_actual_109715 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109715) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_109715
    g32p_supplierForest_actual_107816

def g32p_supplierForest_node_109719 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109719 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109719 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_152639 := by
  decide +kernel

theorem g32p_supplierForest_actual_109719 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109719) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_109719
    g32p_supplierForest_actual_152639

def g32p_supplierForest_node_109738 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109738 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_115812 := by
  decide +kernel

theorem g32p_supplierForest_actual_109738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109738) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_109738
    g32p_supplierForest_actual_115812

def g32p_supplierForest_node_109744 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109744 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109744 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_107889 := by
  decide +kernel

theorem g32p_supplierForest_actual_109744 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109744) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_109744
    g32p_supplierForest_actual_107889

def g32p_supplierForest_node_109756 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_109756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109756 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_042562 := by
  decide +kernel

theorem g32p_supplierForest_actual_109756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109756) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_109756
    g32p_supplierForest_actual_042562

def g32p_supplierForest_node_109789 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_109789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109789 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108954 := by
  decide +kernel

theorem g32p_supplierForest_actual_109789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109789) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_109789
    g32p_supplierForest_actual_108954

def g32p_supplierForest_node_109793 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109793 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109793 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_028759 := by
  decide +kernel

theorem g32p_supplierForest_actual_109793 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109793) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_109793
    g32p_supplierForest_actual_028759

def g32p_supplierForest_node_109832 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_109832 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109832 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115906 := by
  decide +kernel

theorem g32p_supplierForest_actual_109832 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109832) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_109832
    g32p_supplierForest_actual_115906

def g32p_supplierForest_node_109834 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109834 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109834 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115554 := by
  decide +kernel

theorem g32p_supplierForest_actual_109834 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109834) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_109834
    g32p_supplierForest_actual_115554

def g32p_supplierForest_node_109839 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_109839 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109839 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121689 := by
  decide +kernel

theorem g32p_supplierForest_actual_109839 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109839) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_109839
    g32p_supplierForest_actual_121689

def g32p_supplierForest_node_109851 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109851 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109851 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108409 := by
  decide +kernel

theorem g32p_supplierForest_actual_109851 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109851) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_109851
    g32p_supplierForest_actual_108409

def g32p_supplierForest_node_109905 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109905 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109905 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_122195 := by
  decide +kernel

theorem g32p_supplierForest_actual_109905 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109905) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_109905
    g32p_supplierForest_actual_122195

def g32p_supplierForest_node_109924 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109924 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109924 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113018 := by
  decide +kernel

theorem g32p_supplierForest_actual_109924 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109924) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_109924
    g32p_supplierForest_actual_113018

def g32p_supplierForest_node_109942 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109942 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109942 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026477 := by
  decide +kernel

theorem g32p_supplierForest_actual_109942 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109942) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_109942
    g32p_supplierForest_actual_026477

def g32p_supplierForest_node_109958 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_109958 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109958 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039952 := by
  decide +kernel

theorem g32p_supplierForest_actual_109958 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109958) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_109958
    g32p_supplierForest_actual_039952

def g32p_supplierForest_node_109997 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_109997 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_109997 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103271 := by
  decide +kernel

theorem g32p_supplierForest_actual_109997 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_109997) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_109997
    g32p_supplierForest_actual_103271

def g32p_supplierForest_node_110006 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110006 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110006 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042579 := by
  decide +kernel

theorem g32p_supplierForest_actual_110006 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110006) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_110006
    g32p_supplierForest_actual_042579

def g32p_supplierForest_node_110010 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_110010 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110010 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_103494 := by
  decide +kernel

theorem g32p_supplierForest_actual_110010 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110010) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_110010
    g32p_supplierForest_actual_103494

def g32p_supplierForest_node_110040 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110040 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_036754 := by
  decide +kernel

theorem g32p_supplierForest_actual_110040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110040) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_110040
    g32p_supplierForest_actual_036754

def g32p_supplierForest_node_110042 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110042 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110042 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108840 := by
  decide +kernel

theorem g32p_supplierForest_actual_110042 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110042) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_110042
    g32p_supplierForest_actual_108840

def g32p_supplierForest_node_110044 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110044 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110044 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_040432 := by
  decide +kernel

theorem g32p_supplierForest_actual_110044 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110044) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_110044
    g32p_supplierForest_actual_040432

def g32p_supplierForest_node_110061 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110061 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_154352 := by
  decide +kernel

theorem g32p_supplierForest_actual_110061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110061) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 1 g32p_supplierForest_edge_110061
    g32p_supplierForest_actual_154352

def g32p_supplierForest_node_110063 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110063 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110063 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_108884 := by
  decide +kernel

theorem g32p_supplierForest_actual_110063 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110063) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_110063
    g32p_supplierForest_actual_108884

def g32p_supplierForest_node_110070 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_110070 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110070 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_034051 := by
  decide +kernel

theorem g32p_supplierForest_actual_110070 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110070) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_110070
    g32p_supplierForest_actual_034051

def g32p_supplierForest_node_110098 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_110098 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110098 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_125772 := by
  decide +kernel

theorem g32p_supplierForest_actual_110098 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110098) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_110098
    g32p_supplierForest_actual_125772

def g32p_supplierForest_node_110107 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_110107 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110107 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_042007 := by
  decide +kernel

theorem g32p_supplierForest_actual_110107 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110107) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_110107
    g32p_supplierForest_actual_042007

def g32p_supplierForest_node_110112 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_110112 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110112 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_040394 := by
  decide +kernel

theorem g32p_supplierForest_actual_110112 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110112) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 3 g32p_supplierForest_edge_110112
    g32p_supplierForest_actual_040394

def g32p_supplierForest_node_110123 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110123 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110123 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_121792 := by
  decide +kernel

theorem g32p_supplierForest_actual_110123 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110123) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_110123
    g32p_supplierForest_actual_121792

def g32p_supplierForest_node_110132 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110132 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110132 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102982 := by
  decide +kernel

theorem g32p_supplierForest_actual_110132 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110132) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_110132
    g32p_supplierForest_actual_102982

def g32p_supplierForest_node_110143 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_110143 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110143 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_026707 := by
  decide +kernel

theorem g32p_supplierForest_actual_110143 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110143) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_110143
    g32p_supplierForest_actual_026707

def g32p_supplierForest_node_110177 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110177 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110177 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106426 := by
  decide +kernel

theorem g32p_supplierForest_actual_110177 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110177) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_110177
    g32p_supplierForest_actual_106426

def g32p_supplierForest_node_110210 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_110210 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110210 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_106154 := by
  decide +kernel

theorem g32p_supplierForest_actual_110210 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110210) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_110210
    g32p_supplierForest_actual_106154

def g32p_supplierForest_node_110216 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110216 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110216 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_109579 := by
  decide +kernel

theorem g32p_supplierForest_actual_110216 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110216) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_110216
    g32p_supplierForest_actual_109579

def g32p_supplierForest_node_110237 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110237 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110237 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_119642 := by
  decide +kernel

theorem g32p_supplierForest_actual_110237 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110237) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_110237
    g32p_supplierForest_actual_119642

def g32p_supplierForest_node_110239 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110239 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110239 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_109675 := by
  decide +kernel

theorem g32p_supplierForest_actual_110239 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110239) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_110239
    g32p_supplierForest_actual_109675

def g32p_supplierForest_node_110249 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_110249 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110249 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110169 := by
  decide +kernel

theorem g32p_supplierForest_actual_110249 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110249) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_110249
    g32p_supplierForest_actual_110169

def g32p_supplierForest_node_110291 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_110291 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110291 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118440 := by
  decide +kernel

theorem g32p_supplierForest_actual_110291 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110291) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_110291
    g32p_supplierForest_actual_118440

def g32p_supplierForest_node_110293 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110293 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110293 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_041260 := by
  decide +kernel

theorem g32p_supplierForest_actual_110293 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110293) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_110293
    g32p_supplierForest_actual_041260

def g32p_supplierForest_node_110302 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110302 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110302 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_032930 := by
  decide +kernel

theorem g32p_supplierForest_actual_110302 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110302) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_110302
    g32p_supplierForest_actual_032930

def g32p_supplierForest_node_110336 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110336 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110336 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123040 := by
  decide +kernel

theorem g32p_supplierForest_actual_110336 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110336) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_110336
    g32p_supplierForest_actual_123040

def g32p_supplierForest_node_110411 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110411 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110411 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104058 := by
  decide +kernel

theorem g32p_supplierForest_actual_110411 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110411) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_110411
    g32p_supplierForest_actual_104058

def g32p_supplierForest_node_110415 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_110415 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110415 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_102729 := by
  decide +kernel

theorem g32p_supplierForest_actual_110415 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110415) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_110415
    g32p_supplierForest_actual_102729

def g32p_supplierForest_node_110433 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_110433 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110433 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_111655 := by
  decide +kernel

theorem g32p_supplierForest_actual_110433 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110433) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_110433
    g32p_supplierForest_actual_111655

def g32p_supplierForest_node_110531 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_110531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110531 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109416 := by
  decide +kernel

theorem g32p_supplierForest_actual_110531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110531) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_110531
    g32p_supplierForest_actual_109416

def g32p_supplierForest_node_110534 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110534 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_116160 := by
  decide +kernel

theorem g32p_supplierForest_actual_110534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110534) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_110534
    g32p_supplierForest_actual_116160

def g32p_supplierForest_node_110535 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110535 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110535 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_114232 := by
  decide +kernel

theorem g32p_supplierForest_actual_110535 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110535) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_110535
    g32p_supplierForest_actual_114232

def g32p_supplierForest_node_110572 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110572 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110572 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_042220 := by
  decide +kernel

theorem g32p_supplierForest_actual_110572 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110572) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_110572
    g32p_supplierForest_actual_042220

def g32p_supplierForest_node_110597 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110597 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110597 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120714 := by
  decide +kernel

theorem g32p_supplierForest_actual_110597 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110597) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_110597
    g32p_supplierForest_actual_120714

def g32p_supplierForest_node_110606 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110606 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110606 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029810 := by
  decide +kernel

theorem g32p_supplierForest_actual_110606 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110606) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 2 g32p_supplierForest_edge_110606
    g32p_supplierForest_actual_029810

def g32p_supplierForest_node_110626 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110626 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110626 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121927 := by
  decide +kernel

theorem g32p_supplierForest_actual_110626 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110626) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_110626
    g32p_supplierForest_actual_121927

def g32p_supplierForest_node_110664 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110664 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110664 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_035375 := by
  decide +kernel

theorem g32p_supplierForest_actual_110664 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110664) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_110664
    g32p_supplierForest_actual_035375

def g32p_supplierForest_node_110686 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_110686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110686 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_113434 := by
  decide +kernel

theorem g32p_supplierForest_actual_110686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110686) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_110686
    g32p_supplierForest_actual_113434

def g32p_supplierForest_node_110724 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_110724 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110724 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124689 := by
  decide +kernel

theorem g32p_supplierForest_actual_110724 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110724) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_110724
    g32p_supplierForest_actual_124689

def g32p_supplierForest_node_110726 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110726 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110726 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_039119 := by
  decide +kernel

theorem g32p_supplierForest_actual_110726 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110726) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_110726
    g32p_supplierForest_actual_039119

def g32p_supplierForest_node_110821 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110821 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110821 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105747 := by
  decide +kernel

theorem g32p_supplierForest_actual_110821 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110821) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_110821
    g32p_supplierForest_actual_105747

def g32p_supplierForest_node_110832 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110832 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110832 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_031848 := by
  decide +kernel

theorem g32p_supplierForest_actual_110832 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110832) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_110832
    g32p_supplierForest_actual_031848

def g32p_supplierForest_node_110844 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_110844 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110844 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_034658 := by
  decide +kernel

theorem g32p_supplierForest_actual_110844 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110844) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_110844
    g32p_supplierForest_actual_034658

def g32p_supplierForest_node_110872 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110872 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110872 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114869 := by
  decide +kernel

theorem g32p_supplierForest_actual_110872 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110872) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_110872
    g32p_supplierForest_actual_114869

def g32p_supplierForest_node_110874 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_110874 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110874 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_117382 := by
  decide +kernel

theorem g32p_supplierForest_actual_110874 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110874) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_110874
    g32p_supplierForest_actual_117382

def g32p_supplierForest_node_110923 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_110923 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110923 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111946 := by
  decide +kernel

theorem g32p_supplierForest_actual_110923 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110923) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_110923
    g32p_supplierForest_actual_111946

def g32p_supplierForest_node_110929 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_110929 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110929 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120927 := by
  decide +kernel

theorem g32p_supplierForest_actual_110929 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110929) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_110929
    g32p_supplierForest_actual_120927

def g32p_supplierForest_node_110963 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_110963 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_110963 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110964 := by
  decide +kernel

theorem g32p_supplierForest_actual_110963 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_110963) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_110963
    g32p_supplierForest_actual_110964

def g32p_supplierForest_node_111011 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111011 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111011 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106743 := by
  decide +kernel

theorem g32p_supplierForest_actual_111011 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111011) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_111011
    g32p_supplierForest_actual_106743

def g32p_supplierForest_node_111030 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111030 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111030 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_110329 := by
  decide +kernel

theorem g32p_supplierForest_actual_111030 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111030) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_111030
    g32p_supplierForest_actual_110329

def g32p_supplierForest_node_111037 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111037 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111037 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112206 := by
  decide +kernel

theorem g32p_supplierForest_actual_111037 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111037) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_111037
    g32p_supplierForest_actual_112206

def g32p_supplierForest_node_111057 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_111057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111057 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111043 := by
  decide +kernel

theorem g32p_supplierForest_actual_111057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111057) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_111057
    g32p_supplierForest_actual_111043

def g32p_supplierForest_node_111059 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111059 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_027853 := by
  decide +kernel

theorem g32p_supplierForest_actual_111059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111059) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 2 g32p_supplierForest_edge_111059
    g32p_supplierForest_actual_027853

def g32p_supplierForest_node_111071 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111071 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043805 := by
  decide +kernel

theorem g32p_supplierForest_actual_111071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111071) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_111071
    g32p_supplierForest_actual_043805

def g32p_supplierForest_node_111110 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111110 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111110 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043602 := by
  decide +kernel

theorem g32p_supplierForest_actual_111110 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111110) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_111110
    g32p_supplierForest_actual_043602

def g32p_supplierForest_node_111127 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111127 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111127 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043726 := by
  decide +kernel

theorem g32p_supplierForest_actual_111127 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111127) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_111127
    g32p_supplierForest_actual_043726

def g32p_supplierForest_node_111130 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_111130 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111130 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118547 := by
  decide +kernel

theorem g32p_supplierForest_actual_111130 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111130) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_111130
    g32p_supplierForest_actual_118547

def g32p_supplierForest_node_111172 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111172 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111172 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112450 := by
  decide +kernel

theorem g32p_supplierForest_actual_111172 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111172) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 2 g32p_supplierForest_edge_111172
    g32p_supplierForest_actual_112450

def g32p_supplierForest_node_111243 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111243 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111243 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111230 := by
  decide +kernel

theorem g32p_supplierForest_actual_111243 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111243) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_111243
    g32p_supplierForest_actual_111230

def g32p_supplierForest_node_111251 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111251 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111251 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_106069 := by
  decide +kernel

theorem g32p_supplierForest_actual_111251 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111251) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_111251
    g32p_supplierForest_actual_106069

def g32p_supplierForest_node_111299 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111299 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111299 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_033547 := by
  decide +kernel

theorem g32p_supplierForest_actual_111299 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111299) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_111299
    g32p_supplierForest_actual_033547

def g32p_supplierForest_node_111364 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111364 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111364 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_105447 := by
  decide +kernel

theorem g32p_supplierForest_actual_111364 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111364) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_111364
    g32p_supplierForest_actual_105447

def g32p_supplierForest_node_111380 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111380 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111380 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112886 := by
  decide +kernel

theorem g32p_supplierForest_actual_111380 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111380) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_111380
    g32p_supplierForest_actual_112886

def g32p_supplierForest_node_111398 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111398 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111398 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112928 := by
  decide +kernel

theorem g32p_supplierForest_actual_111398 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111398) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_111398
    g32p_supplierForest_actual_112928

def g32p_supplierForest_node_111423 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111423 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111423 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121774 := by
  decide +kernel

theorem g32p_supplierForest_actual_111423 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111423) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 1 g32p_supplierForest_edge_111423
    g32p_supplierForest_actual_121774

def g32p_supplierForest_node_111494 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_111494 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111494 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029579 := by
  decide +kernel

theorem g32p_supplierForest_actual_111494 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111494) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 3 g32p_supplierForest_edge_111494
    g32p_supplierForest_actual_029579

def g32p_supplierForest_node_111515 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111515 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111515 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_119145 := by
  decide +kernel

theorem g32p_supplierForest_actual_111515 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111515) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_111515
    g32p_supplierForest_actual_119145

def g32p_supplierForest_node_111522 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111522 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111230 := by
  decide +kernel

theorem g32p_supplierForest_actual_111522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111522) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_111522
    g32p_supplierForest_actual_111230

def g32p_supplierForest_node_111591 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_111591 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111591 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118084 := by
  decide +kernel

theorem g32p_supplierForest_actual_111591 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111591) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 2 g32p_supplierForest_edge_111591
    g32p_supplierForest_actual_118084

def g32p_supplierForest_node_111598 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_111598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111598 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108037 := by
  decide +kernel

theorem g32p_supplierForest_actual_111598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111598) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_111598
    g32p_supplierForest_actual_108037

def g32p_supplierForest_node_111599 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111599 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111599 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113418 := by
  decide +kernel

theorem g32p_supplierForest_actual_111599 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111599) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_111599
    g32p_supplierForest_actual_113418

def g32p_supplierForest_node_111605 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_111605 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111605 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106761 := by
  decide +kernel

theorem g32p_supplierForest_actual_111605 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111605) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_111605
    g32p_supplierForest_actual_106761

def g32p_supplierForest_node_111626 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_111626 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111626 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_125386 := by
  decide +kernel

theorem g32p_supplierForest_actual_111626 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111626) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_111626
    g32p_supplierForest_actual_125386

def g32p_supplierForest_node_111637 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111637 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111637 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_033835 := by
  decide +kernel

theorem g32p_supplierForest_actual_111637 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111637) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_111637
    g32p_supplierForest_actual_033835

def g32p_supplierForest_node_111654 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111654 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111654 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_110055 := by
  decide +kernel

theorem g32p_supplierForest_actual_111654 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111654) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_111654
    g32p_supplierForest_actual_110055

def g32p_supplierForest_node_111666 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111666 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111666 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_105747 := by
  decide +kernel

theorem g32p_supplierForest_actual_111666 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111666) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 2 g32p_supplierForest_edge_111666
    g32p_supplierForest_actual_105747

def g32p_supplierForest_node_111725 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111725 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111725 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_113274 := by
  decide +kernel

theorem g32p_supplierForest_actual_111725 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111725) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_111725
    g32p_supplierForest_actual_113274

def g32p_supplierForest_node_111752 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_111752 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111752 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_111714 := by
  decide +kernel

theorem g32p_supplierForest_actual_111752 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111752) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_111752
    g32p_supplierForest_actual_111714

def g32p_supplierForest_node_111771 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_111771 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111771 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111740 := by
  decide +kernel

theorem g32p_supplierForest_actual_111771 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111771) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_111771
    g32p_supplierForest_actual_111740

def g32p_supplierForest_node_111773 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_111773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111773 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_153715 := by
  decide +kernel

theorem g32p_supplierForest_actual_111773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111773) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_111773
    g32p_supplierForest_actual_153715

def g32p_supplierForest_node_111796 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_111796 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111796 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_113969 := by
  decide +kernel

theorem g32p_supplierForest_actual_111796 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111796) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_111796
    g32p_supplierForest_actual_113969

def g32p_supplierForest_node_111858 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_111858 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111858 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108012 := by
  decide +kernel

theorem g32p_supplierForest_actual_111858 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111858) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_111858
    g32p_supplierForest_actual_108012

def g32p_supplierForest_node_111873 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111873 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111873 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118480 := by
  decide +kernel

theorem g32p_supplierForest_actual_111873 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111873) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_111873
    g32p_supplierForest_actual_118480

def g32p_supplierForest_node_111895 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_111895 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111895 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_110802 := by
  decide +kernel

theorem g32p_supplierForest_actual_111895 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111895) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_111895
    g32p_supplierForest_actual_110802

def g32p_supplierForest_node_111899 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111899 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111899 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_033971 := by
  decide +kernel

theorem g32p_supplierForest_actual_111899 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111899) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 0 g32p_supplierForest_edge_111899
    g32p_supplierForest_actual_033971

def g32p_supplierForest_node_111916 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_111916 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111916 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106937 := by
  decide +kernel

theorem g32p_supplierForest_actual_111916 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111916) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_111916
    g32p_supplierForest_actual_106937

def g32p_supplierForest_node_111975 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_111975 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111975 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_121196 := by
  decide +kernel

theorem g32p_supplierForest_actual_111975 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111975) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 2 g32p_supplierForest_edge_111975
    g32p_supplierForest_actual_121196

def g32p_supplierForest_node_111984 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_111984 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_111984 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118811 := by
  decide +kernel

theorem g32p_supplierForest_actual_111984 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_111984) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_111984
    g32p_supplierForest_actual_118811

def g32p_supplierForest_node_112062 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112062 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112062 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121755 := by
  decide +kernel

theorem g32p_supplierForest_actual_112062 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112062) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_112062
    g32p_supplierForest_actual_121755

def g32p_supplierForest_node_112151 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112151 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112151 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117248 := by
  decide +kernel

theorem g32p_supplierForest_actual_112151 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112151) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_112151
    g32p_supplierForest_actual_117248

def g32p_supplierForest_node_112166 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_112166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112166 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_111655 := by
  decide +kernel

theorem g32p_supplierForest_actual_112166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112166) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_112166
    g32p_supplierForest_actual_111655

def g32p_supplierForest_node_112286 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112286 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112286 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032225 := by
  decide +kernel

theorem g32p_supplierForest_actual_112286 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112286) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_112286
    g32p_supplierForest_actual_032225

def g32p_supplierForest_node_112360 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112360 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109800 := by
  decide +kernel

theorem g32p_supplierForest_actual_112360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112360) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_112360
    g32p_supplierForest_actual_109800

def g32p_supplierForest_node_112380 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112380 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112380 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_121332 := by
  decide +kernel

theorem g32p_supplierForest_actual_112380 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112380) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_112380
    g32p_supplierForest_actual_121332

def g32p_supplierForest_node_112394 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_112394 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112394 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_104442 := by
  decide +kernel

theorem g32p_supplierForest_actual_112394 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112394) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_112394
    g32p_supplierForest_actual_104442

def g32p_supplierForest_node_112399 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112399 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112399 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_039704 := by
  decide +kernel

theorem g32p_supplierForest_actual_112399 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112399) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_112399
    g32p_supplierForest_actual_039704

def g32p_supplierForest_node_112410 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_112410 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112410 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_109172 := by
  decide +kernel

theorem g32p_supplierForest_actual_112410 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112410) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_112410
    g32p_supplierForest_actual_109172

def g32p_supplierForest_node_112413 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112413 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112413 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118940 := by
  decide +kernel

theorem g32p_supplierForest_actual_112413 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112413) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_112413
    g32p_supplierForest_actual_118940

def g32p_supplierForest_node_112466 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112466 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112466 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112181 := by
  decide +kernel

theorem g32p_supplierForest_actual_112466 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112466) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 1 g32p_supplierForest_edge_112466
    g32p_supplierForest_actual_112181

def g32p_supplierForest_node_112482 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112482 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112482 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_122769 := by
  decide +kernel

theorem g32p_supplierForest_actual_112482 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112482) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_112482
    g32p_supplierForest_actual_122769

def g32p_supplierForest_node_112511 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112511 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112511 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121870 := by
  decide +kernel

theorem g32p_supplierForest_actual_112511 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112511) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_112511
    g32p_supplierForest_actual_121870

def g32p_supplierForest_node_112517 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112517 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112517 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_119752 := by
  decide +kernel

theorem g32p_supplierForest_actual_112517 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112517) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_112517
    g32p_supplierForest_actual_119752

def g32p_supplierForest_node_112526 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112526 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112526 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108787 := by
  decide +kernel

theorem g32p_supplierForest_actual_112526 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112526) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_112526
    g32p_supplierForest_actual_108787

def g32p_supplierForest_node_112567 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112567 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112567 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043715 := by
  decide +kernel

theorem g32p_supplierForest_actual_112567 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112567) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_112567
    g32p_supplierForest_actual_043715

def g32p_supplierForest_node_112585 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112585 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_113165 := by
  decide +kernel

theorem g32p_supplierForest_actual_112585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112585) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_112585
    g32p_supplierForest_actual_113165

def g32p_supplierForest_node_112629 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_112629 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112629 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043301 := by
  decide +kernel

theorem g32p_supplierForest_actual_112629 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112629) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_112629
    g32p_supplierForest_actual_043301

def g32p_supplierForest_node_112634 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112634 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112634 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_153224 := by
  decide +kernel

theorem g32p_supplierForest_actual_112634 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112634) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_112634
    g32p_supplierForest_actual_153224

def g32p_supplierForest_node_112636 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112636 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112636 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109631 := by
  decide +kernel

theorem g32p_supplierForest_actual_112636 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112636) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_112636
    g32p_supplierForest_actual_109631

def g32p_supplierForest_node_112641 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112641 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112641 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_120155 := by
  decide +kernel

theorem g32p_supplierForest_actual_112641 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112641) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_112641
    g32p_supplierForest_actual_120155

def g32p_supplierForest_node_112655 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_112655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112655 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035350 := by
  decide +kernel

theorem g32p_supplierForest_actual_112655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112655) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_112655
    g32p_supplierForest_actual_035350

def g32p_supplierForest_node_112679 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112679 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112679 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108507 := by
  decide +kernel

theorem g32p_supplierForest_actual_112679 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112679) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_112679
    g32p_supplierForest_actual_108507

def g32p_supplierForest_node_112740 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_112740 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112740 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_112738 := by
  decide +kernel

theorem g32p_supplierForest_actual_112740 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112740) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_112740
    g32p_supplierForest_actual_112738

def g32p_supplierForest_node_112753 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112753 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112753 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_043351 := by
  decide +kernel

theorem g32p_supplierForest_actual_112753 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112753) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_112753
    g32p_supplierForest_actual_043351

def g32p_supplierForest_node_112789 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_112789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112789 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_105035 := by
  decide +kernel

theorem g32p_supplierForest_actual_112789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112789) ∧
        IsConj g (g32p_literalRepresentative 58) := by
  exact g32p_archive_step_lift _ _ 58 0 g32p_supplierForest_edge_112789
    g32p_supplierForest_actual_105035

def g32p_supplierForest_node_112830 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112830 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112830 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_115595 := by
  decide +kernel

theorem g32p_supplierForest_actual_112830 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112830) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_112830
    g32p_supplierForest_actual_115595

def g32p_supplierForest_node_112856 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_112856 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112856 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106319 := by
  decide +kernel

theorem g32p_supplierForest_actual_112856 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112856) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 3 g32p_supplierForest_edge_112856
    g32p_supplierForest_actual_106319

def g32p_supplierForest_node_112897 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112897 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112897 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121578 := by
  decide +kernel

theorem g32p_supplierForest_actual_112897 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112897) ∧
        IsConj g (g32p_literalRepresentative 32) := by
  exact g32p_archive_step_lift _ _ 32 0 g32p_supplierForest_edge_112897
    g32p_supplierForest_actual_121578

def g32p_supplierForest_node_112908 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_112908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112908 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_124956 := by
  decide +kernel

theorem g32p_supplierForest_actual_112908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112908) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_112908
    g32p_supplierForest_actual_124956

def g32p_supplierForest_node_112966 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_112966 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112966 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_037538 := by
  decide +kernel

theorem g32p_supplierForest_actual_112966 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112966) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 3 g32p_supplierForest_edge_112966
    g32p_supplierForest_actual_037538

def g32p_supplierForest_node_112975 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_112975 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112975 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115511 := by
  decide +kernel

theorem g32p_supplierForest_actual_112975 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112975) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_112975
    g32p_supplierForest_actual_115511

def g32p_supplierForest_node_112984 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_112984 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_112984 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_123259 := by
  decide +kernel

theorem g32p_supplierForest_actual_112984 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_112984) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_112984
    g32p_supplierForest_actual_123259

def g32p_supplierForest_node_113015 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113015 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113015 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_115526 := by
  decide +kernel

theorem g32p_supplierForest_actual_113015 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113015) ∧
        IsConj g (g32p_literalRepresentative 14) := by
  exact g32p_archive_step_lift _ _ 14 3 g32p_supplierForest_edge_113015
    g32p_supplierForest_actual_115526

def g32p_supplierForest_node_113059 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113059 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103112 := by
  decide +kernel

theorem g32p_supplierForest_actual_113059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113059) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_113059
    g32p_supplierForest_actual_103112

def g32p_supplierForest_node_113070 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_113070 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113070 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113196 := by
  decide +kernel

theorem g32p_supplierForest_actual_113070 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113070) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_113070
    g32p_supplierForest_actual_113196

def g32p_supplierForest_node_113087 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113087 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113087 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_039143 := by
  decide +kernel

theorem g32p_supplierForest_actual_113087 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113087) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_113087
    g32p_supplierForest_actual_039143

def g32p_supplierForest_node_113095 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113095 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_118656 := by
  decide +kernel

theorem g32p_supplierForest_actual_113095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113095) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 3 g32p_supplierForest_edge_113095
    g32p_supplierForest_actual_118656

def g32p_supplierForest_node_113106 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113106 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113106 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_032456 := by
  decide +kernel

theorem g32p_supplierForest_actual_113106 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113106) ∧
        IsConj g (g32p_literalRepresentative 64) := by
  exact g32p_archive_step_lift _ _ 64 2 g32p_supplierForest_edge_113106
    g32p_supplierForest_actual_032456

def g32p_supplierForest_node_113163 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113163 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113163 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115134 := by
  decide +kernel

theorem g32p_supplierForest_actual_113163 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113163) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_113163
    g32p_supplierForest_actual_115134

def g32p_supplierForest_node_113170 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_113170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113170 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_123361 := by
  decide +kernel

theorem g32p_supplierForest_actual_113170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113170) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 2 g32p_supplierForest_edge_113170
    g32p_supplierForest_actual_123361

def g32p_supplierForest_node_113209 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113209 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113209 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_030820 := by
  decide +kernel

theorem g32p_supplierForest_actual_113209 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113209) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113209
    g32p_supplierForest_actual_030820

def g32p_supplierForest_node_113232 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_113232 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113232 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_044101 := by
  decide +kernel

theorem g32p_supplierForest_actual_113232 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113232) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_113232
    g32p_supplierForest_actual_044101

def g32p_supplierForest_node_113239 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113239 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113239 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_034891 := by
  decide +kernel

theorem g32p_supplierForest_actual_113239 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113239) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_113239
    g32p_supplierForest_actual_034891

def g32p_supplierForest_node_113270 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113270 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_042905 := by
  decide +kernel

theorem g32p_supplierForest_actual_113270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113270) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_113270
    g32p_supplierForest_actual_042905

def g32p_supplierForest_node_113345 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113345 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113345 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104661 := by
  decide +kernel

theorem g32p_supplierForest_actual_113345 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113345) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_113345
    g32p_supplierForest_actual_104661

def g32p_supplierForest_node_113354 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_113354 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113354 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_043948 := by
  decide +kernel

theorem g32p_supplierForest_actual_113354 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113354) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_113354
    g32p_supplierForest_actual_043948

def g32p_supplierForest_node_113369 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_113369 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113369 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122627 := by
  decide +kernel

theorem g32p_supplierForest_actual_113369 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113369) ∧
        IsConj g (g32p_literalRepresentative 61) := by
  exact g32p_archive_step_lift _ _ 61 0 g32p_supplierForest_edge_113369
    g32p_supplierForest_actual_122627

def g32p_supplierForest_node_113380 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_113380 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113380 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_104108 := by
  decide +kernel

theorem g32p_supplierForest_actual_113380 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113380) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_113380
    g32p_supplierForest_actual_104108

def g32p_supplierForest_node_113396 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113396 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113396 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_113205 := by
  decide +kernel

theorem g32p_supplierForest_actual_113396 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113396) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_113396
    g32p_supplierForest_actual_113205

def g32p_supplierForest_node_113416 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113416 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113416 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_152948 := by
  decide +kernel

theorem g32p_supplierForest_actual_113416 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113416) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_113416
    g32p_supplierForest_actual_152948

def g32p_supplierForest_node_113445 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_113445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113445 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_108821 := by
  decide +kernel

theorem g32p_supplierForest_actual_113445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113445) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_113445
    g32p_supplierForest_actual_108821

def g32p_supplierForest_node_113482 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113482 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113482 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035836 := by
  decide +kernel

theorem g32p_supplierForest_actual_113482 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113482) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113482
    g32p_supplierForest_actual_035836

def g32p_supplierForest_node_113497 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113497 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113497 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103323 := by
  decide +kernel

theorem g32p_supplierForest_actual_113497 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113497) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_113497
    g32p_supplierForest_actual_103323

def g32p_supplierForest_node_113516 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113516 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113516 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_114270 := by
  decide +kernel

theorem g32p_supplierForest_actual_113516 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113516) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_113516
    g32p_supplierForest_actual_114270

def g32p_supplierForest_node_113522 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113522 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112039 := by
  decide +kernel

theorem g32p_supplierForest_actual_113522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113522) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_113522
    g32p_supplierForest_actual_112039

def g32p_supplierForest_node_113527 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113527 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113527 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122738 := by
  decide +kernel

theorem g32p_supplierForest_actual_113527 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113527) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 0 g32p_supplierForest_edge_113527
    g32p_supplierForest_actual_122738

def g32p_supplierForest_node_113558 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113558 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113558 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109479 := by
  decide +kernel

theorem g32p_supplierForest_actual_113558 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113558) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_113558
    g32p_supplierForest_actual_109479

def g32p_supplierForest_node_113562 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113562 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113562 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109500 := by
  decide +kernel

theorem g32p_supplierForest_actual_113562 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113562) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 1 g32p_supplierForest_edge_113562
    g32p_supplierForest_actual_109500

def g32p_supplierForest_node_113598 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113598 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124693 := by
  decide +kernel

theorem g32p_supplierForest_actual_113598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113598) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 2 g32p_supplierForest_edge_113598
    g32p_supplierForest_actual_124693

def g32p_supplierForest_node_113669 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113669 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113669 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108899 := by
  decide +kernel

theorem g32p_supplierForest_actual_113669 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113669) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_113669
    g32p_supplierForest_actual_108899

def g32p_supplierForest_node_113673 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113673 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113673 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112937 := by
  decide +kernel

theorem g32p_supplierForest_actual_113673 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113673) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_113673
    g32p_supplierForest_actual_112937

def g32p_supplierForest_node_113677 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_113677 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113677 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_031766 := by
  decide +kernel

theorem g32p_supplierForest_actual_113677 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113677) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_113677
    g32p_supplierForest_actual_031766

def g32p_supplierForest_node_113701 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113701 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113701 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_039522 := by
  decide +kernel

theorem g32p_supplierForest_actual_113701 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113701) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_113701
    g32p_supplierForest_actual_039522

def g32p_supplierForest_node_113712 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_113712 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113712 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_121411 := by
  decide +kernel

theorem g32p_supplierForest_actual_113712 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113712) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 0 g32p_supplierForest_edge_113712
    g32p_supplierForest_actual_121411

def g32p_supplierForest_node_113723 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_113723 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113723 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108560 := by
  decide +kernel

theorem g32p_supplierForest_actual_113723 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113723) ∧
        IsConj g (g32p_literalRepresentative 15) := by
  exact g32p_archive_step_lift _ _ 15 1 g32p_supplierForest_edge_113723
    g32p_supplierForest_actual_108560

def g32p_supplierForest_node_113752 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_113752 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113752 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_035169 := by
  decide +kernel

theorem g32p_supplierForest_actual_113752 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113752) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113752
    g32p_supplierForest_actual_035169

def g32p_supplierForest_node_113764 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113764 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113764 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_037327 := by
  decide +kernel

theorem g32p_supplierForest_actual_113764 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113764) ∧
        IsConj g (g32p_literalRepresentative 34) := by
  exact g32p_archive_step_lift _ _ 34 3 g32p_supplierForest_edge_113764
    g32p_supplierForest_actual_037327

def g32p_supplierForest_node_113769 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_113769 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113769 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_114281 := by
  decide +kernel

theorem g32p_supplierForest_actual_113769 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113769) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_113769
    g32p_supplierForest_actual_114281

def g32p_supplierForest_node_113795 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113795 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113795 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037678 := by
  decide +kernel

theorem g32p_supplierForest_actual_113795 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113795) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_113795
    g32p_supplierForest_actual_037678

def g32p_supplierForest_node_113805 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_113805 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113805 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_103336 := by
  decide +kernel

theorem g32p_supplierForest_actual_113805 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113805) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_113805
    g32p_supplierForest_actual_103336

def g32p_supplierForest_node_113824 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_113824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113824 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_029317 := by
  decide +kernel

theorem g32p_supplierForest_actual_113824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113824) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 2 g32p_supplierForest_edge_113824
    g32p_supplierForest_actual_029317

def g32p_supplierForest_node_113825 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113825 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113825 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_042375 := by
  decide +kernel

theorem g32p_supplierForest_actual_113825 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113825) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_113825
    g32p_supplierForest_actual_042375

def g32p_supplierForest_node_113831 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_113831 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113831 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_041971 := by
  decide +kernel

theorem g32p_supplierForest_actual_113831 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113831) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_113831
    g32p_supplierForest_actual_041971

def g32p_supplierForest_node_113839 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113839 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113839 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_115554 := by
  decide +kernel

theorem g32p_supplierForest_actual_113839 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113839) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_113839
    g32p_supplierForest_actual_115554

def g32p_supplierForest_node_113840 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113840 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113840 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103576 := by
  decide +kernel

theorem g32p_supplierForest_actual_113840 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113840) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_113840
    g32p_supplierForest_actual_103576

def g32p_supplierForest_node_113842 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113842 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113842 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112904 := by
  decide +kernel

theorem g32p_supplierForest_actual_113842 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113842) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_113842
    g32p_supplierForest_actual_112904

def g32p_supplierForest_node_113849 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113849 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113849 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_108606 := by
  decide +kernel

theorem g32p_supplierForest_actual_113849 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113849) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_113849
    g32p_supplierForest_actual_108606

def g32p_supplierForest_node_113850 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113850 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113850 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122341 := by
  decide +kernel

theorem g32p_supplierForest_actual_113850 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113850) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_113850
    g32p_supplierForest_actual_122341

def g32p_supplierForest_node_113872 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113872 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113872 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118223 := by
  decide +kernel

theorem g32p_supplierForest_actual_113872 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113872) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 2 g32p_supplierForest_edge_113872
    g32p_supplierForest_actual_118223

def g32p_supplierForest_node_113882 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_113882 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113882 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044198 := by
  decide +kernel

theorem g32p_supplierForest_actual_113882 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113882) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_113882
    g32p_supplierForest_actual_044198

def g32p_supplierForest_node_113892 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113892 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113892 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_116176 := by
  decide +kernel

theorem g32p_supplierForest_actual_113892 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113892) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_113892
    g32p_supplierForest_actual_116176

def g32p_supplierForest_node_113908 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_113908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113908 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_125989 := by
  decide +kernel

theorem g32p_supplierForest_actual_113908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113908) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_113908
    g32p_supplierForest_actual_125989

def g32p_supplierForest_node_113939 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113939 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113939 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113933 := by
  decide +kernel

theorem g32p_supplierForest_actual_113939 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113939) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113939
    g32p_supplierForest_actual_113933

def g32p_supplierForest_node_113961 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_113961 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113961 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_117272 := by
  decide +kernel

theorem g32p_supplierForest_actual_113961 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113961) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_113961
    g32p_supplierForest_actual_117272

def g32p_supplierForest_node_113965 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_113965 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_113965 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_112284 := by
  decide +kernel

theorem g32p_supplierForest_actual_113965 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_113965) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_113965
    g32p_supplierForest_actual_112284

def g32p_supplierForest_node_114071 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_114071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114071 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_024609 := by
  decide +kernel

theorem g32p_supplierForest_actual_114071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114071) ∧
        IsConj g (g32p_literalRepresentative 4) := by
  exact g32p_archive_step_lift _ _ 4 3 g32p_supplierForest_edge_114071
    g32p_supplierForest_actual_024609

def g32p_supplierForest_node_114087 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_114087 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114087 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_041044 := by
  decide +kernel

theorem g32p_supplierForest_actual_114087 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114087) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_114087
    g32p_supplierForest_actual_041044

def g32p_supplierForest_node_114101 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114101 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114101 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_125498 := by
  decide +kernel

theorem g32p_supplierForest_actual_114101 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114101) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_114101
    g32p_supplierForest_actual_125498

def g32p_supplierForest_node_114113 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_114113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114113 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123178 := by
  decide +kernel

theorem g32p_supplierForest_actual_114113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114113) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_114113
    g32p_supplierForest_actual_123178

def g32p_supplierForest_node_114129 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114129 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114129 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_115237 := by
  decide +kernel

theorem g32p_supplierForest_actual_114129 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114129) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_114129
    g32p_supplierForest_actual_115237

def g32p_supplierForest_node_114132 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_114132 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114132 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_122979 := by
  decide +kernel

theorem g32p_supplierForest_actual_114132 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114132) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 0 g32p_supplierForest_edge_114132
    g32p_supplierForest_actual_122979

def g32p_supplierForest_node_114167 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114167 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114167 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_040240 := by
  decide +kernel

theorem g32p_supplierForest_actual_114167 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114167) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 0 g32p_supplierForest_edge_114167
    g32p_supplierForest_actual_040240

def g32p_supplierForest_node_114227 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114227 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114227 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_028822 := by
  decide +kernel

theorem g32p_supplierForest_actual_114227 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114227) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_114227
    g32p_supplierForest_actual_028822

def g32p_supplierForest_node_114243 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_114243 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114243 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117224 := by
  decide +kernel

theorem g32p_supplierForest_actual_114243 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114243) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_114243
    g32p_supplierForest_actual_117224

def g32p_supplierForest_node_114267 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114267 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114267 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_026337 := by
  decide +kernel

theorem g32p_supplierForest_actual_114267 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114267) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_114267
    g32p_supplierForest_actual_026337

def g32p_supplierForest_node_114291 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114291 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114291 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_114289 := by
  decide +kernel

theorem g32p_supplierForest_actual_114291 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114291) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_114291
    g32p_supplierForest_actual_114289

def g32p_supplierForest_node_114314 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114314 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114314 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_043074 := by
  decide +kernel

theorem g32p_supplierForest_actual_114314 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114314) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 2 g32p_supplierForest_edge_114314
    g32p_supplierForest_actual_043074

def g32p_supplierForest_node_114315 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114315 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114315 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_036103 := by
  decide +kernel

theorem g32p_supplierForest_actual_114315 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114315) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_114315
    g32p_supplierForest_actual_036103

def g32p_supplierForest_node_114319 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_114319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114319 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_118387 := by
  decide +kernel

theorem g32p_supplierForest_actual_114319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114319) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_114319
    g32p_supplierForest_actual_118387

def g32p_supplierForest_node_114334 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114334 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_034156 := by
  decide +kernel

theorem g32p_supplierForest_actual_114334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114334) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 1 g32p_supplierForest_edge_114334
    g32p_supplierForest_actual_034156

def g32p_supplierForest_node_114340 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114340 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114340 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104585 := by
  decide +kernel

theorem g32p_supplierForest_actual_114340 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114340) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 0 g32p_supplierForest_edge_114340
    g32p_supplierForest_actual_104585

def g32p_supplierForest_node_114382 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_114382 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114382 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_034638 := by
  decide +kernel

theorem g32p_supplierForest_actual_114382 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114382) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 1 g32p_supplierForest_edge_114382
    g32p_supplierForest_actual_034638

def g32p_supplierForest_node_114396 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114396 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114396 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_035750 := by
  decide +kernel

theorem g32p_supplierForest_actual_114396 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114396) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_114396
    g32p_supplierForest_actual_035750

def g32p_supplierForest_node_114413 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_114413 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114413 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_036491 := by
  decide +kernel

theorem g32p_supplierForest_actual_114413 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114413) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_114413
    g32p_supplierForest_actual_036491

def g32p_supplierForest_node_114420 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114420 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114420 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_025970 := by
  decide +kernel

theorem g32p_supplierForest_actual_114420 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114420) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_114420
    g32p_supplierForest_actual_025970

def g32p_supplierForest_node_114445 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114445 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123368 := by
  decide +kernel

theorem g32p_supplierForest_actual_114445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114445) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_114445
    g32p_supplierForest_actual_123368

def g32p_supplierForest_node_114468 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114468 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114468 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123373 := by
  decide +kernel

theorem g32p_supplierForest_actual_114468 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114468) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 0 g32p_supplierForest_edge_114468
    g32p_supplierForest_actual_123373

def g32p_supplierForest_node_114487 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114487 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114487 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_124476 := by
  decide +kernel

theorem g32p_supplierForest_actual_114487 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114487) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_114487
    g32p_supplierForest_actual_124476

def g32p_supplierForest_node_114490 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114490 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114490 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126436 := by
  decide +kernel

theorem g32p_supplierForest_actual_114490 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114490) ∧
        IsConj g (g32p_literalRepresentative 35) := by
  exact g32p_archive_step_lift _ _ 35 3 g32p_supplierForest_edge_114490
    g32p_supplierForest_actual_126436

def g32p_supplierForest_node_114499 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114499 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114499 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_117727 := by
  decide +kernel

theorem g32p_supplierForest_actual_114499 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114499) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_114499
    g32p_supplierForest_actual_117727

def g32p_supplierForest_node_114504 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_114504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114504 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_038967 := by
  decide +kernel

theorem g32p_supplierForest_actual_114504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114504) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 1 g32p_supplierForest_edge_114504
    g32p_supplierForest_actual_038967

def g32p_supplierForest_node_114547 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_114547 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114547 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_109949 := by
  decide +kernel

theorem g32p_supplierForest_actual_114547 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114547) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_114547
    g32p_supplierForest_actual_109949

def g32p_supplierForest_node_114587 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114587 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114587 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_106042 := by
  decide +kernel

theorem g32p_supplierForest_actual_114587 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114587) ∧
        IsConj g (g32p_literalRepresentative 62) := by
  exact g32p_archive_step_lift _ _ 62 0 g32p_supplierForest_edge_114587
    g32p_supplierForest_actual_106042

def g32p_supplierForest_node_114588 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_114588 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114588 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_109685 := by
  decide +kernel

theorem g32p_supplierForest_actual_114588 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114588) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_114588
    g32p_supplierForest_actual_109685

def g32p_supplierForest_node_114621 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_114621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114621 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118135 := by
  decide +kernel

theorem g32p_supplierForest_actual_114621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114621) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_114621
    g32p_supplierForest_actual_118135

def g32p_supplierForest_node_114664 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_114664 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114664 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_126171 := by
  decide +kernel

theorem g32p_supplierForest_actual_114664 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114664) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 3 g32p_supplierForest_edge_114664
    g32p_supplierForest_actual_126171

def g32p_supplierForest_node_114690 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114690 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114690 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_037647 := by
  decide +kernel

theorem g32p_supplierForest_actual_114690 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114690) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_114690
    g32p_supplierForest_actual_037647

def g32p_supplierForest_node_114701 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114701 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114701 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_113196 := by
  decide +kernel

theorem g32p_supplierForest_actual_114701 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114701) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_114701
    g32p_supplierForest_actual_113196

def g32p_supplierForest_node_114716 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_114716 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114716 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112552 := by
  decide +kernel

theorem g32p_supplierForest_actual_114716 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114716) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 2 g32p_supplierForest_edge_114716
    g32p_supplierForest_actual_112552

def g32p_supplierForest_node_114744 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_114744 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114744 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_036053 := by
  decide +kernel

theorem g32p_supplierForest_actual_114744 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114744) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 0 g32p_supplierForest_edge_114744
    g32p_supplierForest_actual_036053

def g32p_supplierForest_node_114748 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114748 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114748 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_102821 := by
  decide +kernel

theorem g32p_supplierForest_actual_114748 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114748) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 0 g32p_supplierForest_edge_114748
    g32p_supplierForest_actual_102821

def g32p_supplierForest_node_114755 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_114755 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114755 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_041040 := by
  decide +kernel

theorem g32p_supplierForest_actual_114755 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114755) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_114755
    g32p_supplierForest_actual_041040

def g32p_supplierForest_node_114761 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_114761 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114761 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_116575 := by
  decide +kernel

theorem g32p_supplierForest_actual_114761 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114761) ∧
        IsConj g (g32p_literalRepresentative 91) := by
  exact g32p_archive_step_lift _ _ 91 1 g32p_supplierForest_edge_114761
    g32p_supplierForest_actual_116575

def g32p_supplierForest_node_114770 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_114770 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114770 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_106757 := by
  decide +kernel

theorem g32p_supplierForest_actual_114770 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114770) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 3 g32p_supplierForest_edge_114770
    g32p_supplierForest_actual_106757

def g32p_supplierForest_node_114797 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114797 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114797 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_123656 := by
  decide +kernel

theorem g32p_supplierForest_actual_114797 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114797) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_114797
    g32p_supplierForest_actual_123656

def g32p_supplierForest_node_114843 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114843 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114843 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_104617 := by
  decide +kernel

theorem g32p_supplierForest_actual_114843 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114843) ∧
        IsConj g (g32p_literalRepresentative 36) := by
  exact g32p_archive_step_lift _ _ 36 0 g32p_supplierForest_edge_114843
    g32p_supplierForest_actual_104617

def g32p_supplierForest_node_114861 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114861 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114861 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_104852 := by
  decide +kernel

theorem g32p_supplierForest_actual_114861 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114861) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 3 g32p_supplierForest_edge_114861
    g32p_supplierForest_actual_104852

def g32p_supplierForest_node_114864 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114864 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114864 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_030180 := by
  decide +kernel

theorem g32p_supplierForest_actual_114864 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114864) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_114864
    g32p_supplierForest_actual_030180

def g32p_supplierForest_node_114866 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114866 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114866 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_043367 := by
  decide +kernel

theorem g32p_supplierForest_actual_114866 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114866) ∧
        IsConj g (g32p_literalRepresentative 16) := by
  exact g32p_archive_step_lift _ _ 16 3 g32p_supplierForest_edge_114866
    g32p_supplierForest_actual_043367

def g32p_supplierForest_node_114905 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_114905 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114905 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_123682 := by
  decide +kernel

theorem g32p_supplierForest_actual_114905 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114905) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 0 g32p_supplierForest_edge_114905
    g32p_supplierForest_actual_123682

def g32p_supplierForest_node_114917 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114917 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114917 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_029698 := by
  decide +kernel

theorem g32p_supplierForest_actual_114917 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114917) ∧
        IsConj g (g32p_literalRepresentative 59) := by
  exact g32p_archive_step_lift _ _ 59 3 g32p_supplierForest_edge_114917
    g32p_supplierForest_actual_029698

def g32p_supplierForest_node_114927 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_114927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114927 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027733 := by
  decide +kernel

theorem g32p_supplierForest_actual_114927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114927) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_114927
    g32p_supplierForest_actual_027733

def g32p_supplierForest_node_114966 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_114966 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114966 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_118867 := by
  decide +kernel

theorem g32p_supplierForest_actual_114966 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114966) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 2 g32p_supplierForest_edge_114966
    g32p_supplierForest_actual_118867

def g32p_supplierForest_node_114968 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_114968 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_114968 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118134 := by
  decide +kernel

theorem g32p_supplierForest_actual_114968 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_114968) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 1 g32p_supplierForest_edge_114968
    g32p_supplierForest_actual_118134

def g32p_supplierForest_node_115011 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115011 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115011 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_112300 := by
  decide +kernel

theorem g32p_supplierForest_actual_115011 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115011) ∧
        IsConj g (g32p_literalRepresentative 33) := by
  exact g32p_archive_step_lift _ _ 33 2 g32p_supplierForest_edge_115011
    g32p_supplierForest_actual_112300

def g32p_supplierForest_node_115026 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_115026 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115026 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_113221 := by
  decide +kernel

theorem g32p_supplierForest_actual_115026 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115026) ∧
        IsConj g (g32p_literalRepresentative 57) := by
  exact g32p_archive_step_lift _ _ 57 3 g32p_supplierForest_edge_115026
    g32p_supplierForest_actual_113221

def g32p_supplierForest_node_115031 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115031 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115031 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_042518 := by
  decide +kernel

theorem g32p_supplierForest_actual_115031 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115031) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_115031
    g32p_supplierForest_actual_042518

def g32p_supplierForest_node_115032 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_115032 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115032 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118748 := by
  decide +kernel

theorem g32p_supplierForest_actual_115032 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115032) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 1 g32p_supplierForest_edge_115032
    g32p_supplierForest_actual_118748

def g32p_supplierForest_node_115054 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115054 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115054 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_027754 := by
  decide +kernel

theorem g32p_supplierForest_actual_115054 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115054) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_115054
    g32p_supplierForest_actual_027754

def g32p_supplierForest_node_115057 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115057 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_119587 := by
  decide +kernel

theorem g32p_supplierForest_actual_115057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115057) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 2 g32p_supplierForest_edge_115057
    g32p_supplierForest_actual_119587

def g32p_supplierForest_node_115060 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_115060 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115060 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_111928 := by
  decide +kernel

theorem g32p_supplierForest_actual_115060 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115060) ∧
        IsConj g (g32p_literalRepresentative 29) := by
  exact g32p_archive_step_lift _ _ 29 3 g32p_supplierForest_edge_115060
    g32p_supplierForest_actual_111928

def g32p_supplierForest_node_115091 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115091 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_105238 := by
  decide +kernel

theorem g32p_supplierForest_actual_115091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115091) ∧
        IsConj g (g32p_literalRepresentative 17) := by
  exact g32p_archive_step_lift _ _ 17 1 g32p_supplierForest_edge_115091
    g32p_supplierForest_actual_105238

def g32p_supplierForest_node_115100 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_115100 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115100 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_118855 := by
  decide +kernel

theorem g32p_supplierForest_actual_115100 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115100) ∧
        IsConj g (g32p_literalRepresentative 60) := by
  exact g32p_archive_step_lift _ _ 60 1 g32p_supplierForest_edge_115100
    g32p_supplierForest_actual_118855

def g32p_supplierForest_node_115102 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115102 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115102 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_102297 := by
  decide +kernel

theorem g32p_supplierForest_actual_115102 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115102) ∧
        IsConj g (g32p_literalRepresentative 63) := by
  exact g32p_archive_step_lift _ _ 63 2 g32p_supplierForest_edge_115102
    g32p_supplierForest_actual_102297

def g32p_supplierForest_node_115187 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_115187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115187 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_103271 := by
  decide +kernel

theorem g32p_supplierForest_actual_115187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115187) ∧
        IsConj g (g32p_literalRepresentative 30) := by
  exact g32p_archive_step_lift _ _ 30 3 g32p_supplierForest_edge_115187
    g32p_supplierForest_actual_103271

def g32p_supplierForest_node_115188 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_115188 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115188 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_103541 := by
  decide +kernel

theorem g32p_supplierForest_actual_115188 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115188) ∧
        IsConj g (g32p_literalRepresentative 66) := by
  exact g32p_archive_step_lift _ _ 66 1 g32p_supplierForest_edge_115188
    g32p_supplierForest_actual_103541

def g32p_supplierForest_node_115190 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_115190 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_115190 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_038795 := by
  decide +kernel

theorem g32p_supplierForest_actual_115190 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_115190) ∧
        IsConj g (g32p_literalRepresentative 3) := by
  exact g32p_archive_step_lift _ _ 3 3 g32p_supplierForest_edge_115190
    g32p_supplierForest_actual_038795

end HodgeLean.Foundations.Program

end
end
